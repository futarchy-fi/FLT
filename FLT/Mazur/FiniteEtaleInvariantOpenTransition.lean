/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteEtaleInvariantOpenBoundary

/-!
# Closed transitions on affine invariant relation domains

A cartesian closed transition between full relations restricts to the exact
inverse image of any invariant open. On an affine such domain, every lower
invariant coefficient lifts through the transition.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteEtaleInvariantOpenTransition
open SchemeEffectiveEpiSections SchemeRelationInvariantSpectrum
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A D' A' : Scheme.{0}} (p q : D ⟶ A) (p' q' : D' ⟶ A')
  (a : A' ⟶ A) (b : D' ⟶ D) (H : IsPullback b p' p a) (hq : b ≫ q = q' ≫ a)
  (U : A.Opens) (hU : p ⁻¹ᵁ U = q ⁻¹ᵁ U)
set_option quotPrecheck false
local notation "V" => a ⁻¹ᵁ U
local notation "r" => p.resLE U _ le_rfl
local notation "s" => q.resLE U _ hU.le
local notation "r'" => p'.resLE V _ le_rfl

include H hq hU in
/-- The exact lower inverse image is invariant under both full endpoints. -/
theorem preimage_invariant : p' ⁻¹ᵁ V = q' ⁻¹ᵁ V := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, ← H.w, ← hq,
    Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage, hU]

include H in
/-- The complete restricted relation maps to the higher restricted relation. -/
theorem domain_le : p' ⁻¹ᵁ V ≤ b ⁻¹ᵁ (p ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, H.w]

/-- Restriction of the entire original transition arrow. -/
def arrow : (p' ⁻¹ᵁ V).toScheme ⟶ (p ⁻¹ᵁ U).toScheme :=
  b.resLE _ _ (domain_le p p' a b H U)

/-- The first endpoint square on the inverse image domain commutes. -/
@[reassoc]
theorem arrow_first : arrow p p' a b H U ≫ r = r' ≫ (a ∣_ U) := by
  apply (cancel_mono U.ι).mp
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι,
    morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc, arrow]
  rw [H.w]

/-- The second endpoint square retains the independent original endpoint. -/
@[reassoc]
theorem arrow_second : arrow p p' a b H U ≫ s =
    q'.resLE V _ (preimage_invariant p q p' q' a b H hq U hU).le ≫ (a ∣_ U) := by
  apply (cancel_mono U.ι).mp
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι,
    morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc, arrow]
  rw [hq]

/-- Restriction preserves the cartesian square for the whole first endpoint. -/
theorem arrow_isPullback : IsPullback (arrow p p' a b H U) r' r (a ∣_ U) := by
  apply IsPullback.of_right _ (arrow_first p p' a b H U)
    (by rw [Scheme.Hom.resLE_eq_morphismRestrict]
        exact (isPullback_morphismRestrict p U).flip)
  rw [arrow, Scheme.Hom.resLE_comp_ι, morphismRestrict_ι]
  have H' : IsPullback (p' ⁻¹ᵁ V).ι r' p' (V).ι := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact (isPullback_morphismRestrict p' V).flip
  exact H'.paste_horiz H

/-- The actual map of full invariant rings on the two restricted source schemes. -/
def restriction := relationPullback r s r'
  (q'.resLE V _ (preimage_invariant p q p' q' a b H hq U hU).le)
  (a ∣_ U) (arrow p p' a b H U) (arrow_first p p' a b H U)
  (arrow_second p q p' q' a b H hq U hU)

variable {S : Scheme.{0}} [IsAffine S] [IsFinite p] [Etale p]
  (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (e : CategoryTheory.EquivalenceRelation p q) [IsClosedImmersion a]

include hf e in
/-- Full lower invariants lift on every affine invariant higher domain. -/
theorem restriction_surjective (ha : IsAffineOpen U) :
    Function.Surjective (restriction p q p' q' a b H hq U hU) := by
  let _ : IsAffine U.toScheme := ha
  let _ : IsAffine (V).toScheme := ha.preimage a
  let _ : IsFinite r := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  have Hr : IsPullback (p ⁻¹ᵁ U).ι r p U.ι := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact (isPullback_morphismRestrict p U).flip
  have Hf : r ≫ (U.ι ≫ f) = s ≫ (U.ι ≫ f) := by
    rw [← Category.assoc, ← Category.assoc, Scheme.Hom.resLE_comp_ι,
      Scheme.Hom.resLE_comp_ι, Category.assoc, Category.assoc, hf]
  exact AffineFiniteEtaleBoundarySurjectivity.boundary_invariant_surjective
    r s (U.ι ≫ f) Hf (EquivalenceRelationFiber.invariantRestrictionEquivalence e Hr
      (Scheme.Hom.resLE_comp_ι q hU.le).symm) _ _ _ _
    (arrow_isPullback p p' a b H U) (arrow_second p q p' q' a b H hq U hU)

end FLT.Mazur.FiniteEtaleInvariantOpenTransition
