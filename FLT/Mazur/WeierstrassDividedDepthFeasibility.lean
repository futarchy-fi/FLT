/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedExactCoefficientDepth

/-!
# Feasible depths of actual divided coefficient data

The constant coefficient has exact node depth. Consequently division data
at depth k can exist only if twice k is at most the node depth. This also
checks whether final-stage hypotheses in an addition theorem are realizable.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
variable {R : Type*} [CommRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth k : ℕ}
  (node : SplitNodeDepth W π depth) (d : Data W π k)

include node d in
/-- Actual coefficient division cannot extend beyond half the exact constant depth. -/
theorem data_twice_depth_le : 2 * k ≤ depth := by
  by_contra h
  have hp : π ^ (2 * k) ∈ maximalIdeal R ^ (2 * k) :=
    Ideal.pow_mem_pow (node.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π) (2 * k)
  have hc : W.a₆ ∈ maximalIdeal R ^ (2 * k) := by
    have hf : W.a₆ = π ^ (2 * k) * d.b6 := by
      simpa only [← pow_mul, Nat.mul_comm k 2] using d.factor6
    rw [hf]
    exact Ideal.mul_mem_right _ _ hp
  exact node.a₆_not_mem ((Ideal.pow_le_pow_right (by omega : depth + 1 ≤ 2 * k)) hc)

variable {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (0 + i.val))

include node data

/-- A supplied family itself bounds the largest possible resolved stage. -/
theorem dataFamily_twice_last_le : 2 * n ≤ depth := by
  simpa only [Nat.zero_add] using data_twice_depth_le node (data ⟨n, Nat.lt_succ_self n⟩)

/-- Any selected stage of that family lies at or below the actual middle. -/
theorem dataFamily_twice_stage_le (j : ℕ) (hj : j ≤ n) : 2 * j ≤ depth := by
  have h := dataFamily_twice_last_le node data
  omega

/-- A doubled output-stage bound excludes every strictly sub-fourfold node depth. -/
theorem dataFamily_doubled_stage_fourfold (j d : ℕ) (hj : j ≤ n) (hd : 2 * d ≤ j) :
    4 * d ≤ depth := by
  have h := dataFamily_twice_stage_le node data j hj
  omega

end FLT.Mazur.WeierstrassDividedDepth
