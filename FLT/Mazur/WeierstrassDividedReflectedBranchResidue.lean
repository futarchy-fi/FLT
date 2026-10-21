/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReflectedBranchFormula

/-!
# Reflected output residues with positive terminal residual depth

When the common scale vanishes, the exact constant quotient controls the
output abscissa. The output is on the negative branch and its vertical
derivative is nonzero, including in residue characteristic two.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
variable {K : Type*} [Field K] (W : WeierstrassCurve K) (c6 x u q r i : K)
  (hxu : IsUnit (x * u))
local notation "X" => reflectedBranchX 0 0 c6 x u q r i hxu
local notation "Y" => reflectedBranchY W 0 0 0 c6 0 x u q r i 0 hxu

/-- The exact constant quotient gives the entire leading reflected abscissa. -/
theorem reflectedBranchX_residue : X * (x * u) = -c6 := by
  unfold reflectedBranchX
  rw [mul_assoc, hxu.val_inv_mul]
  ring

/-- The constructed reflected abscissa is nonzero on punctured inputs. -/
theorem reflectedBranchX_residue_ne_zero (hc6 : c6 ≠ 0) : X ≠ 0 := by
  intro h
  have he := reflectedBranchX_residue c6 x u q r i hxu
  rw [h, zero_mul] at he
  exact hc6 (neg_eq_zero.mp he.symm)

/-- Beyond the middle, positive inputs produce the negative reflected branch. -/
theorem reflectedBranchY_residue : Y = -W.a₁ * X := by
  simp only [reflectedBranchY, zero_add, zero_mul, sub_zero]

/-- The reflected derivative is nonzero in every residue characteristic. -/
theorem reflectedBranch_residue_vertical (ha : W.a₁ ≠ 0) (hc6 : c6 ≠ 0) :
    2 * Y + W.a₁ * X ≠ 0 := by
  rw [reflectedBranchY_residue]
  have he : 2 * (-W.a₁ * X) + W.a₁ * X = -W.a₁ * X := by ring
  rw [he]
  exact mul_ne_zero (neg_ne_zero.mpr ha)
    (reflectedBranchX_residue_ne_zero c6 x u q r i hxu hc6)

end FLT.Mazur.WeierstrassDilatation
