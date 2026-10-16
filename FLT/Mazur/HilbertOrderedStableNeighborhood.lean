/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrderedAffineEnvelope
public import FLT.Mazur.HilbertCompleteGeometricTuple

/-!
# Complete geometric frames in permutation-stable affine neighborhoods

Every original geometric point has a complete frame factoring through an
actual affine open preserved by every permutation. Completeness is retained
at the distinguished geometric test; completeness throughout the neighborhood
is a separate condition and is not asserted here.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
open RelativeOrderedTuples
local notation "E" => fullRelationOverFirst f hL d V c k
variable {K : Type} [Field K] [IsSepClosed K] (b : Spec (.of K) ⟶ A.left)

/-- Complete geometric frames have actual stable affine neighborhoods on the original scheme. -/
theorem exists_fullRelation_complete_stable_affine_tuple :
    ∃ (n : ℕ) (a : Over.mk b ⟶ fullRelationOrderedPoints f hL d V c k n)
      (U : (fullRelationOrderedPoints f hL d V c k n).left.Opens)
      (z : Spec (.of K) ⟶ U.toScheme),
      Function.Bijective (fun i ↦ geometricCoordinate E (Fin n) a i default) ∧
      IsAffineOpen U ∧
      (∀ e : Equiv.Perm (Fin n),
        (fullRelationOrderedAction f hL d V c k n e).hom ⁻¹ᵁ U = U) ∧
      Etale (U.ι ≫ (fullRelationOrderedPoints f hL d V c k n).hom) ∧
      z ≫ U.ι = a.left ∧
      z ≫ U.ι ≫ (fullRelationOrderedPoints f hL d V c k n).hom = b := by
  let _ : Inhabited (Over.mk b).left := inferInstanceAs (Inhabited (Spec (.of K)))
  let _ : Subsingleton (Over.mk b).left := inferInstanceAs (Subsingleton (Spec (.of K)))
  obtain ⟨n, a, ha⟩ := exists_fullRelation_complete_tuple f hL d V c k b
  obtain ⟨U, hU, hx, he⟩ :=
    exists_fullRelation_ordered_stable_affine f hL d V c k n (a.left default)
  have hr : Set.range a.left ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    change a.left y ∈ U
    rw [Subsingleton.elim y default]
    exact hx
  let z := IsOpenImmersion.lift U.ι a.left hr
  have hz : z ≫ U.ι = a.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨n, a, U, z, ha, hU, he, inferInstance, hz, ?_⟩
  rw [← Category.assoc, hz]
  exact a.w

end FLT.Mazur.HilbertChart.AffineRestriction
