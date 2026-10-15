/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertAcyclicLift
public import FLT.Mazur.AffineHilbertChartRelation

/-!
# Original relation arrows from acyclic classes and chart retention

The original Hilbert parameter is constructed from the translated divisor
class. If its image lies in the chosen open source, it lifts to that source
and then to the full original relation. The resulting arrow has exactly the
supplied independent envelope coordinates, on arbitrary scheme tests.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
  {T : Over (Spec (.of R))} (b : T ⟶ A) (v : T ⟶ V)
local notation "σ" => sectionAt f hL d V c k
local notation "s" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) σ

/-- A constructed Hilbert parameter retained in the original open gives an actual source map. -/
theorem exists_acyclic_source_lift
    (hs : s * (relativeFppfSheaf f).obj.map v.op c ∈
      (acyclicDegreePicardSubfunctor f d).obj (op T))
    (hr : Set.range (acyclicTranslationLift f hL d V c s v hs).left ⊆ Set.range k.left) :
    ∃ a : T ⟶ A, a ≫ k = acyclicTranslationLift f hL d V c s v hs ∧
      a ≫ k ≫ variableHilbertBase f d V = v ∧
      (relativeFppfSheaf f).obj.map a.op σ = s := by
  let l := acyclicTranslationLift f hL d V c s v hs
  let a₀ := IsOpenImmersion.lift k.left l.left hr
  have ha₀ : a₀ ≫ k.left = l.left := IsOpenImmersion.lift_fac k.left l.left hr
  have hw : a₀ ≫ A.hom = T.hom := by
    rw [← k.w, ← Category.assoc, ha₀, l.w]
  let a : T ⟶ A := Over.homMk a₀ hw
  have ha : a ≫ k = l := Over.OverMorphism.ext ha₀
  refine ⟨a, ha, ?_, ?_⟩
  · rw [← Category.assoc, ha]
    exact acyclicTranslationLift_base f hL d V c s v hs
  · change (relativeFppfSheaf f).obj.map a.op
      ((relativeFppfSheaf f).obj.map k.op (variableChartSection f hL d V c)) = s
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, ha]
    exact acyclicTranslationLift_class f hL d V c s v hs

/-- The acyclic divisor construction lifts the whole envelope map to the original relation. -/
theorem exists_acyclic_relation_lift
    (hs : s * (relativeFppfSheaf f).obj.map v.op c ∈
      (acyclicDegreePicardSubfunctor f d).obj (op T))
    (hr : Set.range (acyclicTranslationLift f hL d V c s v hs).left ⊆ Set.range k.left) :
    ∃ z : T ⟶ relation f hL d V c k,
      z ≫ toEnvelope f hL d V c k = prod.lift b v := by
  obtain ⟨a, _, hv, hc⟩ := exists_acyclic_source_lift f hL d V c k b v hs hr
  obtain ⟨z, hz, _⟩ := lift f hL d V c k a b hc
  refine ⟨z, ?_⟩
  apply prod.hom_ext
  · rw [Category.assoc, toEnvelope_test, hz.2, prod.lift_fst]
  · rw [Category.assoc, toEnvelope_base, ← Category.assoc, hz.1, hv, prod.lift_snd]

/-- Over a field, retaining the single constructed point suffices for the entire source map. -/
theorem exists_acyclic_geometric_relation_lift {K : Type} [Field K]
    (hT : T.left = Spec (.of K))
    (hs : s * (relativeFppfSheaf f).obj.map v.op c ∈
      (acyclicDegreePicardSubfunctor f d).obj (op T)) (t : T.left)
    (hr : (acyclicTranslationLift f hL d V c s v hs).left t ∈ Set.range k.left) :
    ∃ z : T ⟶ relation f hL d V c k,
      z ≫ toEnvelope f hL d V c k = prod.lift b v := by
  apply exists_acyclic_relation_lift f hL d V c k b v hs
  let _ : Subsingleton T.left := by
    rw [hT]
    infer_instance
  rintro _ ⟨u, rfl⟩
  rwa [Subsingleton.elim u t]

end FLT.Mazur.HilbertChart.AffineRestriction
