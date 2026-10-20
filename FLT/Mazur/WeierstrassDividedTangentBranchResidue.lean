/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentBranchFormula

/-!
# Residue identities for the strict-branch output

Clearing the two constructed inverses proves the exceptional output formulas.
No cancellation by the scale, input difference, or residue characteristic occurs.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  (s b3 a2 b4' b6' u₁ u₂ v₁ v₂ : R)
  (hc : IsUnit (v₁ + W.a₁ * u₁ + b3))
  (hd : IsUnit (v₁ + v₂ + W.a₁ * u₂ + b3))
local notation "t" => tangentBranchOrdinate W b3 a2 b4' b6' u₁ v₁ hc
local notation "k" => tangentBranchSlope W b3 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd
local notation "X" => tangentBranchX W s a2 u₁ u₂ k
local notation "Y" => tangentBranchY W s b3 a2 u₁ u₂ v₁ k

/-- The branch ordinate satisfies its denominator equation before any specialization. -/
theorem tangentBranchOrdinate_denominator :
    t * (v₁ + W.a₁ * u₁ + b3) = u₁ ^ 3 + a2 * u₁ ^ 2 + b4' * u₁ + b6' := by
  unfold tangentBranchOrdinate
  rw [mul_assoc, hc.val_inv_mul, mul_one]

/-- The divided slope satisfies its denominator equation before any specialization. -/
theorem tangentBranchSlope_denominator :
    k * (v₁ + v₂ + W.a₁ * u₂ + b3) =
      u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2 + a2 * (u₁ + u₂) + b4' - W.a₁ * t := by
  unfold tangentBranchSlope
  rw [mul_assoc, hd.val_inv_mul, mul_one]

/-- The exceptional abscissa is controlled by the next constant coefficient. -/
theorem tangentBranchX_residue (hs : s = 0) (h3 : b3 = 0)
    (h₁ : v₁ = 0) (h₂ : v₂ = 0) : u₁ * u₂ * X = -b6' := by
  subst s b3 v₁ v₂
  have ht := tangentBranchOrdinate_denominator W 0 a2 b4' b6' u₁ 0 hc
  have hk := tangentBranchSlope_denominator W 0 a2 b4' b6' u₁ u₂ 0 0 hc hd
  simp only [zero_add, add_zero] at ht hk
  simp only [tangentBranchX, zero_mul, zero_add]
  linear_combination u₁ * hk - ht

/-- The output lies on the opposite strict branch of the exceptional equation. -/
theorem tangentBranchY_residue (hs : s = 0) (h3 : b3 = 0) (h₁ : v₁ = 0) :
    Y = -W.a₁ * X := by
  simp only [tangentBranchY, hs, h3, h₁, zero_mul, zero_add, sub_zero, add_zero]

end FLT.Mazur.WeierstrassDilatation
