/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.Field

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!+# Nonarchimedean Tate coordinate series

The two coordinate series are indexed by the integers. Their positive tails tend to
zero when the powers of `q` do; inversion of the rational summands gives the same
conclusion for their negative tails. Completeness and the nonarchimedean topology
then give unconditional convergence.

The correction term is `∑_{n ≥ 1} qⁿ/(1-qⁿ)²`, the Lambert-series expression for
`s₁(q)`. These coordinates have poles at `q^ℤ`; totalized division assigns junk
values there. Constructing points on the Tate curve requires excluding those poles.
-/

@[expose] public section

open Filter
open scoped Topology

namespace TateCurve

section Algebra

variable {K : Type*} [Field K]

/-- The rational summand in the Tate `x`-coordinate. -/
def xTerm (v : K) : K := v / (1 - v) ^ 2

/-- The rational summand in the Tate `y`-coordinate. -/
def yTerm (v : K) : K := v ^ 2 / (1 - v) ^ 3

/-- Inverting the argument preserves the `x` summand, including its junk value at `1`. -/
theorem xTerm_inv {v : K} (hv : v ≠ 0) : xTerm v⁻¹ = xTerm v := by
  by_cases hv1 : v = 1
  · simp [xTerm, hv1]
  · have h1 : 1 - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
    have hi : 1 - v⁻¹ ≠ 0 := by simpa [sub_eq_zero] using hv1
    dsimp [xTerm]
    apply (div_eq_div_iff (pow_ne_zero _ hi) (pow_ne_zero _ h1)).mpr
    field_simp
    ring

/-- Inversion transforms the `y` summand into a rational function vanishing at zero. -/
theorem yTerm_inv {v : K} (hv : v ≠ 0) : yTerm v⁻¹ = -v / (1 - v) ^ 3 := by
  by_cases hv1 : v = 1
  · simp [yTerm, hv1]
  · have h1 : 1 - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
    have hi : 1 - v⁻¹ ≠ 0 := by simpa [sub_eq_zero] using hv1
    dsimp [yTerm]
    apply (div_eq_div_iff (pow_ne_zero _ hi) (pow_ne_zero _ h1)).mpr
    field_simp
    ring

end Algebra

section Convergence

variable {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
  [IsTopologicalDivisionRing K] [NonarchimedeanAddGroup K] [CompleteSpace K]

/-- Rational tails with positive numerator degree are summable when powers of `q`
tend to zero. Finitely many vanishing denominators do not affect summability. -/
theorem summable_tate_tail {q : K}
    (hq : Tendsto (fun n : ℕ ↦ q ^ n) atTop (𝓝 0)) (u : K)
    {j : ℕ} (hj : j ≠ 0) (d : ℕ) :
    Summable (fun n : ℕ ↦ (q ^ n * u) ^ j / (1 - q ^ n * u) ^ d) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop]
  have ht : Tendsto (fun n : ℕ ↦ q ^ n * u) atTop (𝓝 0) := by
    simpa using hq.mul_const u
  simpa [zero_pow hj] using!
    (ht.pow j).div ((tendsto_const_nhds.sub ht).pow d) (by simp)

/-- The integer-indexed series defining the Tate `x`-coordinate converges. -/
theorem summable_tate_x {q u : K} (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq : Tendsto (fun n : ℕ ↦ q ^ n) atTop (𝓝 0)) :
    Summable (fun n : ℤ ↦ xTerm (q ^ n * u)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa [xTerm] using summable_tate_tail hq u (j := 1) one_ne_zero 2
  · have h := summable_tate_tail hq u⁻¹ (j := 1) one_ne_zero 2
    refine h.congr fun n ↦ ?_
    rw [show q ^ (-(n : ℤ)) * u = (q ^ n * u⁻¹)⁻¹ by simp [mul_comm], xTerm_inv
      (mul_ne_zero (pow_ne_zero _ hq0) (inv_ne_zero hu0))]
    simp [xTerm]

/-- The integer-indexed series defining the Tate `y`-coordinate converges. -/
theorem summable_tate_y {q u : K} (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq : Tendsto (fun n : ℕ ↦ q ^ n) atTop (𝓝 0)) :
    Summable (fun n : ℤ ↦ yTerm (q ^ n * u)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa [yTerm] using summable_tate_tail hq u (j := 2) (by decide) 3
  · have h := (summable_tate_tail hq u⁻¹ (j := 1) one_ne_zero 3).neg
    refine h.congr fun n ↦ ?_
    rw [show q ^ (-(n : ℤ)) * u = (q ^ n * u⁻¹)⁻¹ by simp [mul_comm], yTerm_inv
      (mul_ne_zero (pow_ne_zero _ hq0) (inv_ne_zero hu0))]
    simp [neg_div]

/-- The correction series in the Tate coordinates converges. -/
theorem summable_tate_correction {q : K}
    (hq : Tendsto (fun n : ℕ ↦ q ^ n) atTop (𝓝 0)) :
    Summable (fun n : ℕ ↦ xTerm (q ^ (n + 1))) := by
  have h : Summable (fun n : ℕ ↦ xTerm (q ^ n)) := by
    simpa [xTerm] using summable_tate_tail hq 1 (j := 1) one_ne_zero 2
  exact (summable_nat_add_iff (f := fun n : ℕ ↦ xTerm (q ^ n)) 1).mpr h

end Convergence

end TateCurve
