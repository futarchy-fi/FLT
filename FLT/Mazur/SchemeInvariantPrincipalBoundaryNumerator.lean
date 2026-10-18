/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeInvariantPrincipalNumerator

/-!
# Extending exact invariant boundary kernels from principal opens

Clearing the denominator of an invariant section first gives an invariant
numerator. A further power kills its boundary restriction on the original
affine boundary, so the extended correction is exactly boundary zero.
Neither the boundary nor the ambient scheme is replaced by its reduction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme} (i : Y ⟶ X) (s : Γ(X, ⊤))

/-- The actual map between the principal opens cut out by a function and its pullback. -/
def principalPullbackMap :
    (Y.basicOpen (i.appTop s)).toScheme ⟶ (X.basicOpen s).toScheme :=
  i.resLE _ _ (by rw [Scheme.preimage_basicOpen_top])

/-- Principal restriction preserves the original boundary or comparison morphism. -/
@[reassoc] theorem principalPullbackMap_inclusion :
    principalPullbackMap i s ≫ (X.basicOpen s).ι =
      (Y.basicOpen (i.appTop s)).ι ≫ i := Scheme.Hom.resLE_comp_ι _ _

/-- Pullback of a restricted numerator is restriction of its original pullback. -/
theorem principalPullbackMap_appTop (a : Γ(X, ⊤)) :
    (principalPullbackMap i s).appTop ((X.basicOpen s).ι.appTop a) =
      (Y.basicOpen (i.appTop s)).ι.appTop (i.appTop a) := by
  change (principalPullbackMap i s ≫ (X.basicOpen s).ι).appTop a =
    ((Y.basicOpen (i.appTop s)).ι ≫ i).appTop a
  rw [principalPullbackMap_inclusion]

variable {G : Type} [Group G] [Finite G] [IsAffine X] [IsAffine Y]
  (ρ : G →* Aut X) (r : invariantCoordinates ρ)

/-- An exact principal boundary lift extends with the same original scalar power. -/
theorem principal_invariant_boundary_lift_numerator
    (v : invariantCoordinates (principalAction ρ r)) (t : Γ(Y, ⊤))
    (hv : (principalPullbackMap i r.val).appTop v.val =
      (Y.basicOpen (i.appTop r.val)).ι.appTop t) :
    ∃ (n : ℕ) (w : invariantCoordinates ρ),
      i.appTop w.val = (i.appTop r.val) ^ n * t ∧
      (X.basicOpen r.val).ι.appTop w.val =
        ((X.basicOpen r.val).ι.appTop r.val) ^ n * v.val := by
  obtain ⟨n, w, hw⟩ := principal_invariant_numerator ρ r v
  have hb : (Y.basicOpen (i.appTop r.val)).ι.appTop (i.appTop w.val) =
      (Y.basicOpen (i.appTop r.val)).ι.appTop ((i.appTop r.val) ^ n * t) := by
    rw [← principalPullbackMap_appTop, hw]
    simp only [map_mul, map_pow, hv, principalPullbackMap_appTop]
  obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq (i.appTop r.val) hb
  refine ⟨k + n, r ^ k * w, ?_, ?_⟩
  · change i.appTop (r.val ^ k * w.val) = _
    rw [map_mul, map_pow, hk, pow_add, mul_assoc]
  · change (X.basicOpen r.val).ι.appTop (r.val ^ k * w.val) = _
    simp only [map_mul, map_pow, hw, pow_add, mul_assoc]

/-- A principal invariant boundary-kernel element extends after an original scalar power. -/
theorem principal_invariant_boundary_numerator
    (v : invariantCoordinates (principalAction ρ r))
    (hv : (principalPullbackMap i r.val).appTop v.val = 0) :
    ∃ (n : ℕ) (w : invariantCoordinates ρ), i.appTop w.val = 0 ∧
      (X.basicOpen r.val).ι.appTop w.val =
        ((X.basicOpen r.val).ι.appTop r.val) ^ n * v.val := by
  obtain ⟨n, w, hw, he⟩ := principal_invariant_boundary_lift_numerator i ρ r v 0
    (by simpa only [map_zero] using hv)
  exact ⟨n, w, by simpa only [mul_zero] using hw, he⟩

end FLT.Mazur.SchemeFiniteGroupQuotient
