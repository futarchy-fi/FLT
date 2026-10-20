/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentBranchResidue

/-!
# A unit controlling the second divided strict-branch output

When the first constant and fourth coefficient vanish in the residue,
the divided slope and ordinate retain a unit difference. This is the
opposite branch factor of the second divided output, before using its equation.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  (b3 a2 b4' b6' u₁ u₂ v₁ v₂ : R)
  (hc : IsUnit (v₁ + W.a₁ * u₁ + b3))
  (hd : IsUnit (v₁ + v₂ + W.a₁ * u₂ + b3))
local notation "t" => tangentBranchOrdinate W b3 a2 b4' b6' u₁ v₁ hc
local notation "l" => tangentBranchSlope W b3 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd

/-- The second output's opposite branch factor is a unit on the original strict branch. -/
theorem tangentBranch_second_residue_unit (h3 : b3 = 0) (h4 : b4' = 0)
    (h6 : b6' = 0) (h₁ : v₁ = 0) (h₂ : v₂ = 0) : IsUnit (l * u₁ - t) := by
  subst b3 b4' b6' v₁ v₂
  have hcu : IsUnit (W.a₁ * u₁) := by simpa only [zero_add, add_zero] using hc
  have hdu : IsUnit (W.a₁ * u₂) := by simpa only [zero_add, add_zero] using hd
  have hu₁ := isUnit_of_mul_isUnit_right hcu
  have hu₂ := isUnit_of_mul_isUnit_right hdu
  have ht := tangentBranchOrdinate_denominator W 0 a2 0 0 u₁ 0 hc
  have hl := tangentBranchSlope_denominator W 0 a2 0 0 u₁ u₂ 0 0 hc hd
  simp only [zero_add, add_zero, zero_mul] at ht hl
  have ht' : W.a₁ * tangentBranchOrdinate W 0 a2 0 0 u₁ 0 hc = u₁ ^ 2 + a2 * u₁ := by
    apply hu₁.mul_left_inj.mp
    linear_combination ht
  have hl' : W.a₁ * tangentBranchSlope W 0 a2 0 0 u₁ u₂ 0 0 hc hd =
      u₁ + u₂ + a2 := by
    apply hu₂.mul_left_inj.mp
    linear_combination hl - ht'
  have he : W.a₁ * (tangentBranchSlope W 0 a2 0 0 u₁ u₂ 0 0 hc hd * u₁ -
      tangentBranchOrdinate W 0 a2 0 0 u₁ 0 hc) = u₁ * u₂ := by
    linear_combination u₁ * hl' - ht'
  exact isUnit_of_mul_isUnit_right (he.symm ▸ hu₁.mul hu₂)

/-- Cancel the original scale to retain the full second output ordinate identity. -/
theorem tangentBranch_second_ordinate (s b3' X₂ Y₂ : R) (hs : IsRegular s)
    (h3 : b3 = s * b3') (hx : s * X₂ = tangentBranchX W s a2 u₁ u₂ l)
    (hy : s * Y₂ = tangentBranchY W s b3 a2 u₁ u₂ v₁ l) (hv : s * t = v₁) :
    Y₂ = -(s * l + W.a₁) * X₂ + l * u₁ - t - b3' := by
  simp only [tangentBranchY] at hy
  rw [← hx] at hy
  apply hs.left
  linear_combination hy + hv - h3

/-- A unit opposite factor forces a smooth vertical derivative on the residual node. -/
theorem secondBranch_vertical_isUnit {A X Y : R}
    (he : Y ^ 2 + A * X * Y = 0) (hu : IsUnit (Y + A * X)) :
    IsUnit (2 * Y + A * X) := by
  have hy : Y = 0 := by
    apply hu.mul_left_inj.mp
    linear_combination he
  simpa only [hy, mul_zero, zero_add] using hu

end FLT.Mazur.WeierstrassDilatation
