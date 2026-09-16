/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.Odlyzko.PoitouSeries

/-!
# Poitou's series in the large-parameter regime

For the degree-eighteen calculation the useful parameter is larger than the radius `1 / 4`
of equation (22).  Poitou's equation (23) supplies the analytic value of the first term there;
all remaining terms still lie inside the convergence disc.  This file packages exactly that
mixed representation.
-/

@[expose] public section

namespace Odlyzko.Poitou

/-- Poitou's `L₁` for `0 < y < 9/4`: equation (23) for the first term and equation (22)
for every scaled term. -/
noncomputable def L1large (y : ℝ) : ℝ :=
  Lclosed y + ∑' m : ℕ, L1term y (m + 1)

private theorem scaled_lt_quarter {y : ℝ} (hy : y < 9 / 4) (m : ℕ) :
    y / (2 * ((m + 1 : ℕ) : ℝ) + 1) ^ 2 < 1 / 4 := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hd : (9 : ℝ) ≤ (2 * ((m + 1 : ℕ) : ℝ) + 1) ^ 2 := by
    push_cast
    nlinarith
  have hden : (0 : ℝ) < (2 * ((m + 1 : ℕ) : ℝ) + 1) ^ 2 := by positivity
  rw [div_lt_iff₀ hden]
  nlinarith

theorem L1term_shift_nonneg {y : ℝ} (hy0 : 0 < y) (hy : y < 9 / 4) (m : ℕ) :
    0 ≤ L1term y (m + 1) := by
  have hz0 : 0 < y / (2 * (((m + 1 : ℕ) : ℝ)) + 1) ^ 2 := by positivity
  exact mul_nonneg (by positivity) (L_nonneg hz0.le (scaled_lt_quarter hy m))

theorem L1term_shift_le {y : ℝ} (hy0 : 0 < y) (hy : y < 9 / 4) (m : ℕ) :
    L1term y (m + 1) ≤ 4 / 5 * y * oddCube (m + 1) := by
  have hd : (0 : ℝ) < 2 * (((m + 1 : ℕ) : ℝ)) + 1 := by positivity
  have hz0 : 0 < y / (2 * (((m + 1 : ℕ) : ℝ)) + 1) ^ 2 := by positivity
  have hL := L_le hz0 (scaled_lt_quarter hy m)
  calc
    L1term y (m + 1)
        ≤ ((2 * (((m + 1 : ℕ) : ℝ)) + 1))⁻¹ *
            (4 / 5 * (y / (2 * (((m + 1 : ℕ) : ℝ)) + 1) ^ 2)) :=
          mul_le_mul_of_nonneg_left hL (by positivity)
    _ = 4 / 5 * y * oddCube (m + 1) := by
      rw [oddCube]
      push_cast
      field_simp

/-- The shifted series in the large-parameter representation is summable. -/
theorem L1large_tail_summable {y : ℝ} (hy0 : 0 < y) (hy : y < 9 / 4) :
    Summable (fun m : ℕ ↦ L1term y (m + 1)) := by
  refine summable_of_sum_range_le (c := 4 / 5 * y * (1 / 12))
    (fun m ↦ L1term_shift_nonneg hy0 hy m) (fun n ↦ ?_)
  have hy45 : (0 : ℝ) ≤ 4 / 5 * y := by positivity
  calc
    ∑ m ∈ Finset.range n, L1term y (m + 1)
        ≤ ∑ m ∈ Finset.range n, 4 / 5 * y * oddCube (m + 1) :=
          Finset.sum_le_sum fun m _ ↦ L1term_shift_le hy0 hy m
    _ = 4 / 5 * y * ∑ m ∈ Finset.range n, oddCube (m + 1) := by
      rw [Finset.mul_sum]
    _ ≤ 4 / 5 * y * (1 / 12) := by
      gcongr
      exact sum_range_oddCube_shift_le n

/-- The mixed large-`y` representation splits into Poitou's three displayed terms and the
remaining odd-index tail. -/
theorem L1large_eq_head_add_tail {y : ℝ} (hy0 : 0 < y) (hy : y < 9 / 4) :
    L1large y =
      (Lclosed y + 1 / 3 * L (y / 9) + 1 / 5 * L (y / 25)) +
        ∑' m : ℕ, L1term y (m + 3) := by
  have hsplit := (L1large_tail_summable hy0 hy).sum_add_tsum_nat_add 2
  rw [L1large, ← hsplit]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [L1term]
  ring_nf

/-- The tail after the three terms displayed in Poitou's equation (25) is bounded by `y/175`.
The larger range is valid because each tail argument has already been divided by at least `7²`. -/
theorem L1large_tail_le {y : ℝ} (hy0 : 0 < y) (hy : y < 9 / 4) :
    ∑' m : ℕ, L1term y (m + 3) ≤ y / 175 := by
  have hnonneg : ∀ m : ℕ, 0 ≤ L1term y (m + 3) := by
    intro m
    simpa [Nat.add_assoc] using L1term_shift_nonneg hy0 hy (m + 2)
  refine Real.tsum_le_of_sum_range_le hnonneg (fun n ↦ ?_)
  have hy45 : (0 : ℝ) ≤ 4 / 5 * y := by positivity
  calc
    ∑ m ∈ Finset.range n, L1term y (m + 3)
        ≤ ∑ m ∈ Finset.range n, 4 / 5 * y * oddCube (m + 3) := by
          apply Finset.sum_le_sum
          intro m _
          simpa [Nat.add_assoc] using L1term_shift_le hy0 hy (m + 2)
    _ = 4 / 5 * y * ∑ m ∈ Finset.range n, oddCube (m + 3) := by
      rw [Finset.mul_sum]
    _ ≤ 4 / 5 * y * (1 / 140) := by
      gcongr
      exact sum_range_oddCube_tail_le n
    _ = y / 175 := by ring

/-- A convenient upper bound for the mixed large-`y` representation. -/
theorem L1large_le_head_add {y : ℝ} (hy0 : 0 < y) (hy : y < 9 / 4) :
    L1large y ≤ Lclosed y + 1 / 3 * L (y / 9) + 1 / 5 * L (y / 25) + y / 175 := by
  rw [L1large_eq_head_add_tail hy0 hy]
  linarith [L1large_tail_le hy0 hy]

end Odlyzko.Poitou
