/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.GlobalModel
public import FLT.GroupScheme.PadicTensorPatching

/-!
# The rational generic field in the arithmetic square for `ℤ[1/2]`

The arithmetic patching maps to `ℚ₃` agree with the rational embeddings.
The ring away from three has fraction field `ℚ`, while its overlap with
`ℤ₃` is computed inside `ℚ₃`.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan.PadicPatching

local instance : Fact (¬ (3 : ℤ) ∣ 2) := ⟨by norm_num⟩

/-- Embed the ring with two and three inverted into the rational numbers. -/
def awayTwoThreeToRat : Away 2 3 →+* ℚ :=
  IsLocalization.Away.lift (3 : ZInvTwo)
    (show IsUnit (algebraMap ZInvTwo ℚ 3) from
      (by simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (3 : ℚ) ≠ 0))))

instance : Algebra (Away 2 3) ℚ := awayTwoThreeToRat.toAlgebra

instance : IsScalarTower ZInvTwo (Away 2 3) ℚ := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  exact (IsLocalization.Away.lift_eq (3 : ZInvTwo)
    (show IsUnit (algebraMap ZInvTwo ℚ 3) from
      (by simpa only [map_ofNat] using
        (isUnit_iff_ne_zero.mpr (by norm_num : (3 : ℚ) ≠ 0)))) x).symm

instance : IsFractionRing (Away 2 3) ℚ :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (3 : ZInvTwo)) (Away 2 3) ℚ

instance : IsScalarTower ZInvTwo ℚ ℚ_[3] := by
  apply IsScalarTower.of_algebraMap_eq'
  apply IsLocalization.ringHom_ext (Submonoid.powers (2 : ℤ))
  exact Subsingleton.elim _ _

instance : IsScalarTower (Away 2 3) ℚ ℚ_[3] := by
  apply IsScalarTower.of_algebraMap_eq'
  apply IsLocalization.ringHom_ext (Submonoid.powers (3 : ZInvTwo))
  ext x
  simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]

end ThreeAdicPlan.PadicPatching
