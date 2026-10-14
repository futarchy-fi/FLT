/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeParameterTrivialization

/-!
# Iterating the original carry law

The sum of carries along repeated addition is exactly the quotient of the
accumulated natural label by the component period. This gives the original
parameter of every natural multiple without adjoining a period root.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
open IsLocalRing
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n) (c₆ : A)

/-- Count the actual full-period carries while adding the same generic point repeatedly. -/
def nodePointTotalCarry (m : ℕ) (P : (W.map (algebraMap A K)).toProjective.Point) : ℕ :=
  (Finset.range m).sum fun k => nodePointCarry D (k • P) P

/-- Successive actual carries recover the exact unreduced natural label. -/
theorem nodePointLabel_val_nsmul_totalCarry
    (m : ℕ) (P : (W.map (algebraMap A K)).toProjective.Point) :
    (nodePointLabel D (m • P)).val + n * nodePointTotalCarry D m P =
      m * (nodePointLabel D P).val := by
  induction m with
  | zero => simp only [nodePointTotalCarry, Finset.range_zero, Finset.sum_empty,
      zero_nsmul, nodePointLabel_zero, ZMod.val_zero, Nat.mul_zero, Nat.zero_add, Nat.zero_mul]
  | succ m ih =>
    have hc := nodePointLabel_val_add_carry D (m • P) P
    simp only [nodePointTotalCarry, Finset.sum_range_succ] at ih ⊢
    rw [succ_nsmul]
    nlinarith

/-- The total carry is the integer quotient of the accumulated nonnegative input label. -/
theorem nodePointTotalCarry_eq_div
    (m : ℕ) (P : (W.map (algebraMap A K)).toProjective.Point) :
    nodePointTotalCarry D m P = m * (nodePointLabel D P).val / n := by
  have : NeZero n := ⟨Nat.ne_of_gt D.depth_pos⟩
  rw [← nodePointLabel_val_nsmul_totalCarry D m P, Nat.add_mul_div_left _ _ D.depth_pos,
    Nat.div_eq_of_lt (nodePointLabel D (m • P)).val_lt, Nat.zero_add]

/-- Powers of the original unit parameter retain the sum of the actual carries. -/
theorem nodePointParameterUnit_pow_totalCarry (h6 : W.a₆ = π ^ n * c₆)
    (m : ℕ) (P : (W.map (algebraMap A K)).toProjective.Point) :
    nodePointParameterUnit D c₆ h6 P ^ m =
      nodeWrapParameterUnit D c₆ h6 ^ nodePointTotalCarry D m P *
        nodePointParameterUnit D c₆ h6 (m • P) := by
  induction m with
  | zero => simp only [nodePointTotalCarry, Finset.range_zero, Finset.sum_empty,
      pow_zero, zero_nsmul, nodePointParameterUnit_zero, mul_one]
  | succ m ih =>
    rw [pow_succ, ih, mul_assoc, nodePointParameterUnit_carry D c₆ h6 (m • P) P,
      ← mul_assoc, ← pow_add]
    simp only [nodePointTotalCarry, Finset.sum_range_succ, succ_nsmul]

/-- Every natural multiple has the explicit floor-quotient period correction. -/
theorem nodePointParameterUnit_pow (h6 : W.a₆ = π ^ n * c₆)
    (m : ℕ) (P : (W.map (algebraMap A K)).toProjective.Point) :
    nodePointParameterUnit D c₆ h6 P ^ m =
      nodeWrapParameterUnit D c₆ h6 ^ (m * (nodePointLabel D P).val / n) *
        nodePointParameterUnit D c₆ h6 (m • P) := by
  rw [← nodePointTotalCarry_eq_div D m P]
  exact nodePointParameterUnit_pow_totalCarry D c₆ h6 m P

/-- One full period has a correction determined exactly by the input's nonnegative label. -/
theorem nodePointParameterUnit_pow_period (h6 : W.a₆ = π ^ n * c₆)
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    nodePointParameterUnit D c₆ h6 P ^ n =
      nodeWrapParameterUnit D c₆ h6 ^ (nodePointLabel D P).val *
        nodePointParameterUnit D c₆ h6 (n • P) := by
  rw [nodePointParameterUnit_pow D c₆ h6 n P, Nat.mul_div_right _ D.depth_pos]

end FLT.Mazur
