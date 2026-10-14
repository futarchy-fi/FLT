/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeParameterCarryLaw

/-!
# Trivializing the original period with a specified root

A supplied unit whose n-th power is the original period removes the carry
factor. This constructs an actual multiplicative character on all generic
points. Existence of the root and geometric chart identification are not
assumed or hidden in this construction.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
open IsLocalRing
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n) (c₆ : A)

/-- The canonical natural labels add with exactly the recorded full-period carry. -/
theorem nodePointLabel_val_add_carry
    (P Q : (W.map (algebraMap A K)).toProjective.Point) :
    (nodePointLabel D P).val + (nodePointLabel D Q).val =
      (nodePointLabel D (P + Q)).val + n * nodePointCarry D P Q := by
  have : NeZero n := ⟨Nat.ne_of_gt D.depth_pos⟩
  rw [nodePointLabel_add, nodePointCarry]
  split_ifs with h
  · simpa only [Nat.mul_one] using ZMod.val_add_val_of_le h
  · rw [Nat.mul_zero, Nat.add_zero, ZMod.val_add_of_lt (by omega)]

/-- The unit parameter of the original identity is one. -/
@[simp] theorem nodePointParameterUnit_zero (h6 : W.a₆ = π ^ n * c₆) :
    nodePointParameterUnit D c₆ h6 0 = 1 := by
  classical
  apply Units.ext
  rw [nodePointParameterUnit_val]
  change nodePointParameter D c₆ (0 : ellipticE0 A W).val = _
  rw [nodePointParameter_smooth, map_zero]
  rfl

/-- Divide by a chosen period root to the canonical nonnegative label. -/
def nodeTrivializedParameter (h6 : W.a₆ = π ^ n * c₆) (r : (ResidueField A)ˣ)
    (P : (W.map (algebraMap A K)).toProjective.Point) : (ResidueField A)ˣ :=
  nodePointParameterUnit D c₆ h6 P / r ^ (nodePointLabel D P).val

/-- A genuine period root turns the original carry law into ordinary multiplication. -/
theorem nodeTrivializedParameter_add (h6 : W.a₆ = π ^ n * c₆) (r : (ResidueField A)ˣ)
    (hr : r ^ n = nodeWrapParameterUnit D c₆ h6)
    (P Q : (W.map (algebraMap A K)).toProjective.Point) :
    nodeTrivializedParameter D c₆ h6 r (P + Q) =
      nodeTrivializedParameter D c₆ h6 r P * nodeTrivializedParameter D c₆ h6 r Q := by
  dsimp only [nodeTrivializedParameter]
  rw [div_mul_div_comm, ← pow_add, nodePointLabel_val_add_carry D P Q,
    pow_add, pow_mul, hr, nodePointParameterUnit_carry D c₆ h6 P Q]
  rw [mul_comm (nodeWrapParameterUnit D c₆ h6 ^ nodePointCarry D P Q),
    mul_div_mul_right_eq_div]

/-- Trivialization preserves the original identity. -/
@[simp] theorem nodeTrivializedParameter_zero (h6 : W.a₆ = π ^ n * c₆)
    (r : (ResidueField A)ˣ) : nodeTrivializedParameter D c₆ h6 r 0 = 1 := by
  simp only [nodeTrivializedParameter, nodePointParameterUnit_zero, nodePointLabel_zero,
    ZMod.val_zero, pow_zero, div_one]

/-- The trivialized parameter is a character of the actual generic elliptic group. -/
def nodeTrivializedParameterHom (h6 : W.a₆ = π ^ n * c₆) (r : (ResidueField A)ˣ)
    (hr : r ^ n = nodeWrapParameterUnit D c₆ h6) :
    (W.map (algebraMap A K)).toProjective.Point →+ Additive (ResidueField A)ˣ where
  toFun P := Additive.ofMul (nodeTrivializedParameter D c₆ h6 r P)
  map_zero' := congrArg Additive.ofMul (nodeTrivializedParameter_zero D c₆ h6 r)
  map_add' P Q := congrArg Additive.ofMul (nodeTrivializedParameter_add D c₆ h6 r hr P Q)

/-- Trivialization does not alter equality on a specified component. -/
theorem nodeTrivializedParameter_eq_iff (h6 : W.a₆ = π ^ n * c₆)
    (r : (ResidueField A)ˣ) {P Q : (W.map (algebraMap A K)).toProjective.Point}
    (hl : nodePointLabel D P = nodePointLabel D Q) :
    nodeTrivializedParameter D c₆ h6 r P = nodeTrivializedParameter D c₆ h6 r Q ↔
      nodePointParameter D c₆ P = nodePointParameter D c₆ Q := by
  simp only [nodeTrivializedParameter, hl, div_left_inj, ← Units.val_inj,
    nodePointParameterUnit_val]

end FLT.Mazur
