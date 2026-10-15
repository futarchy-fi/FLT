/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertGeometricAcyclicFiber

/-!
# A constructed common geometric test at every original source point

The separable closure of the ORIGINAL residue field supplies the common test;
no geometric point or section family is an input. The sufficient acyclic and
retention conditions can therefore be checked at any original source point.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (A : Over (Spec (.of R))) (x : A.left)
local notation "η" => (default : Spec (CommRingCat.of
  (SeparableClosure (Scheme.residueField (CategoryTheory.Over.left A) x))))

/-- The common geometric test is the separable closure of the original source residue field. -/
def sourceGeometricPoint : Spec (.of (SeparableClosure (A.left.residueField x))) ⟶ A.left :=
  Spec.map (CommRingCat.ofHom (algebraMap (A.left.residueField x) _)) ≫
    A.left.fromSpecResidueField x

/-- The constructed test lies over exactly the original chosen point. -/
theorem sourceGeometricPoint_apply
    (y : Spec (.of (SeparableClosure (A.left.residueField x)))) :
    sourceGeometricPoint A x y = x := by
  exact Scheme.fromSpecResidueField_apply x _

/-- The geometric test retains the unchanged original ground ring. -/
abbrev sourceGeometricTest : Over (Spec (.of R)) :=
  Over.mk (sourceGeometricPoint A x ≫ A.hom)

/-- The actual original source map on the constructed common test. -/
abbrev sourceGeometricMap : sourceGeometricTest A x ⟶ A :=
  Over.homMk (sourceGeometricPoint A x)

/-- Every original independent fiber is enumerated on its constructed common test. -/
theorem exists_independent_geometric_sections_at
    (V : Over (Spec (.of R))) [Etale V.hom] [IsAffine V.left] :
    ∃ e : Fin ((prod.fst : prod A V ⟶ A).left ⁻¹' {x}).ncard →
        (sourceGeometricTest A x ⟶ prod A V),
      (∀ i, e i ≫ prod.fst = sourceGeometricMap A x) ∧
      Function.Injective (fun i ↦ (e i).left η) ∧
      Set.range (fun i ↦ (e i).left η) = (prod.fst : prod A V ⟶ A).left ⁻¹' {x} := by
  have h := exists_independent_geometric_sections V (sourceGeometricMap A x)
  let P (y : A.left) : Prop :=
    ∃ e : Fin ((prod.fst : prod A V ⟶ A).left ⁻¹' {y}).ncard →
        (sourceGeometricTest A x ⟶ prod A V),
      (∀ i, e i ≫ prod.fst = sourceGeometricMap A x) ∧
      Function.Injective (fun i ↦ (e i).left η) ∧
      Set.range (fun i ↦ (e i).left η) = (prod.fst : prod A V ⟶ A).left ⁻¹' {y}
  exact Eq.mp (congrArg P (sourceGeometricPoint_apply A x η)) h

variable [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom] [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "s" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f))
  (Quiver.Hom.op (sourceGeometricMap A x))
  (sectionAt f hL d V c k)

/-- Constructed common-test Hilbert lifts certify fullness at the original point itself. -/
theorem fullEnvelopeLocus_of_source_geometric_test
    (hA : ∀ v : sourceGeometricTest A x ⟶ V, s * (relativeFppfSheaf f).obj.map v.op c ∈
      (acyclicDegreePicardSubfunctor f d).obj (op (sourceGeometricTest A x)))
    (hr : ∀ v : sourceGeometricTest A x ⟶ V,
      (acyclicTranslationLift f hL d V c s v (hA v)).left η ∈ Set.range k.left) :
    x ∈ fullEnvelopeLocus f hL d V c k := by
  have h := fullEnvelopeLocus_of_all_geometric_translations f hL d V c k
    (sourceGeometricMap A x) hA hr
  change sourceGeometricPoint A x η ∈ _ at h
  rwa [sourceGeometricPoint_apply] at h

end FLT.Mazur.HilbertChart.AffineRestriction
