/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Poitou's auxiliary series `L` and `L₁`

This file transcribes the alternating series of Georges Poitou, *Sur les petits discriminants*,
Séminaire Delange-Pisot-Poitou **18** (1976–77), no. 1, exposé 6, and proves the two truncation
bounds the numerical endgame needs.  Every formula below is taken from
`cartography/poitou-1977-transcription.md` §7.3–§7.6, which transcribes the manuscript pages
6-13 … 6-15 directly; the second-hand summary in `cartography/odlyzko-reconciled.md` is **not**
the source of truth for these coefficients.

## The formulas, with their manuscript equation numbers

*Equation (20), p. 6-14.*  For the normalized Tartar test function `f`, the even derivatives at
the origin are
`(-1)^k f^(2k)(0) = 9 · 2^(2k+3) / ((2k+1)(2k+3)(2k+4)(2k+6))`.

*Equation (22), p. 6-15.*  The auxiliary function is the alternating series
`L(y) = 2y|f''(0)| - 2y²|f⁽⁴⁾(0)| + … + (-1)^(k+1) 2y^k |f^(2k)(0)| + …`.
Because (22) carries the factor `2·|f^(2k)(0)|`, the coefficient appearing in `L` is
`c k = 9 · 2^(2k+4) / ((2k+1)(2k+3)(2k+4)(2k+6))` — this is `Odlyzko.Poitou.c` below — so that
`c 1 = 4/5`, `c 2 = 144/175`, `c 3 = 128/105`, matching the printed expansion
`L(y) = (4/5) y - (144/175) y² + …`.  The series converges for `|y| < 1/4`.

*Equation (23), p. 6-15.*  The closed form, valid for larger positive `y` where (22) is
impractical, is `Odlyzko.Poitou.Lclosed` below:
`L(y) = -3/(20y²) + 33/(10y) + 2 + (3/(80y³) + 3/(4y²)) log(1+4y)
        - (3/y + 12/5) arctan(2√y)/√y`.

*Equation (17), p. 6-13.*  `λ(k) = 1 + 3^(-k) + 5^(-k) + … = (1 - 2^(-k)) ζ(k)`.  Here `λ` is
`Odlyzko.Poitou.lambdaOdd`, defined by the `tsum` on the left; the identity with `riemannZeta`
on the right is recorded but not needed by any statement in this file.

*Equation (24), p. 6-15.*  `L₁(y) = L(y) + (1/3)L(y/3²) + (1/5)L(y/5²) + …
  + (r₁/n){L(y) - L(y/2²) + L(y/3²) - …}`.  The campaign's case is totally imaginary, `r₁ = 0`,
so `Odlyzko.Poitou.L1` below is the first row only, indexed by the odd integers `2m+1`.

*Equation (25), p. 6-15.*  Poitou truncates `L₁` after `m = 0, 1, 2` and bounds the tail by
`(4/5) y (λ(3) - 1 - 3⁻³ - 5⁻³) - (144/175) y² (λ(5) - …) + (128/105) y³ (λ(7) - …)`, i.e. by
`0.006762754 · (4/5) y` to first order.  Theorem `L1_tail_le` below proves the weaker but fully
certified bound `y/175`, obtained from `λ(3) - 1 - 3⁻³ - 5⁻³ ≤ 1/140` (`lambdaOdd_three_tail_le`)
— `1/140 = 0.007142…` against Poitou's `0.006762754…`.

*Equation (26), p. 6-15.* **This is the consumer target of this file.**  For every `y > 0`,
`(1/n) log|d| ≥ γ + log(4π) + r₁/n - 12π/(5 n √y) - L₁(y)`, and at `r₁ = 0` the term `L₁(y)` is
independent of the degree `n`.  A later packet turns `L1` below, together with `L1_tail_le` and
`abs_L_sub_Lpartial_le`, into a certified numerical upper bound for `L₁(y₀)` at a fixed `y₀`.

## Relation to `FLT.Odlyzko.ScaledInequality`

`FLT.Odlyzko.ScaledInequality` defines an *abstract* `Odlyzko.L1 (archimedeanIntegral : ℝ → ℂ)`,
the degree-independent part of the bound as a function of whatever archimedean integral the
caller supplies.  The `Odlyzko.Poitou.L1` of this file is the *concrete* series (24) at `r₁ = 0`.
The two are deliberately kept apart: this file proves arithmetic facts about the concrete series
and does not touch `ScaledInequality`.  A later packet is expected to supply the identification
`Odlyzko.L1 archimedeanIntegral y = Odlyzko.Poitou.L1 y` for the Tartar test function — that is,
to instantiate the abstract constant with the series proved here — which is why every statement
below is phrased directly in terms of `L`, `L1` and explicit rational constants, with no
dependence on the explicit formula machinery.

## Numerical cross-check of (23) against (22)

A transcription slip in (23) would propagate silently into the certified evaluation, so the two
forms were compared numerically outside Lean.  At `y = 1/10`:
* the series (22), summed to 400 terms: `L(0.1) = 0.07280640881595…`;
* the closed form (23): `Lclosed(0.1) = 0.07280640881594…`.
They agree to 13 digits.  Further spot checks: `y = 0.2` gives `0.134310746342770` from (22)
against `0.134310746342770` from (23), and `y = 0.05` gives `0.038082677532009` against
`0.038082677532003`.  The manuscript's own consistency check (§7.7) is also reproduced by (23):
`Lclosed(1.7242) = 0.59456807…`, against the paper's `L(y) < 0.5945682`, and
`Lclosed(1.7242) + Lclosed(1.7242/9)/3 + Lclosed(1.7242/25)/5 = 0.64805132…`, against the
paper's `0.5945682 + 0.0431595 + 0.0103233 = 0.648051`.  No Lean statement below depends on
`Lclosed`; it is transcribed here so that the later evaluation packet has it available.

## Main results

* `c_one`, `c_two`, `c_three` : the first three coefficients are `4/5`, `144/175`, `128/105`.
* `c_mul_pow_antitone` : for `0 ≤ y ≤ 1/4` the terms `c k * y ^ k` are antitone in `k`.
* `abs_L_sub_Lpartial_le` : **R4 (i)**, the Leibniz remainder bound
  `|L y - Lpartial y N| ≤ c N * y ^ N` for `0 < y < 1/4` and every `N`.
* `L_nonneg`, `L_le` : `0 ≤ L y ≤ (4/5) * y` on `0 < y < 1/4`.
* `L1_tail_le` : **R4 (ii)**, the `m ≥ 3` tail of (24) is at most `y / 175`, an `O(y)` bound with
  an explicit rational constant.
* `L1_summable`, `L1_eq_head_add_tail` : the series (24) converges and splits as the three
  Poitou head terms plus the tail bounded above.
-/


@[expose] public section

namespace Odlyzko.Poitou

open Filter Topology

/-! ### The coefficients of (22) -/

/-- The denominator `(2k+1)(2k+3)(2k+4)(2k+6)` of Poitou's equation (20). -/
noncomputable def cDen (k : ℕ) : ℝ := (2 * k + 1) * (2 * k + 3) * (2 * k + 4) * (2 * k + 6)

/-- The coefficient of `y ^ k` in Poitou's alternating series (22),
`c k = 9 · 2 ^ (2k+4) / ((2k+1)(2k+3)(2k+4)(2k+6))`.

The exponent is `2k+4` rather than the `2k+3` of equation (20) because (22) is built from
`2 · |f^(2k)(0)|`. -/
noncomputable def c (k : ℕ) : ℝ := 9 * 2 ^ (2 * k + 4) / cDen k

theorem cDen_pos (k : ℕ) : 0 < cDen k := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  unfold cDen
  positivity

theorem c_pos (k : ℕ) : 0 < c k := by
  rw [c]
  exact div_pos (by positivity) (cDen_pos k)

theorem c_nonneg (k : ℕ) : 0 ≤ c k := (c_pos k).le

/-- Sanity check against the printed expansion `L(y) = (4/5) y - (144/175) y² + …`. -/
theorem c_one : c 1 = 4 / 5 := by norm_num [c, cDen]

/-- Sanity check against the printed expansion `L(y) = (4/5) y - (144/175) y² + …`. -/
theorem c_two : c 2 = 144 / 175 := by norm_num [c, cDen]

/-- Sanity check against the term `(128/105) y³` used in Poitou's equation (25). -/
theorem c_three : c 3 = 128 / 105 := by norm_num [c, cDen]

theorem cDen_le_succ (k : ℕ) : cDen k ≤ cDen (k + 1) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  simp only [cDen]
  push_cast
  nlinarith [sq_nonneg ((k : ℝ)), sq_nonneg ((k : ℝ) + 1), mul_nonneg hk hk,
    mul_nonneg (mul_nonneg hk hk) hk]

theorem seventyTwo_le_cDen (k : ℕ) : (72 : ℝ) ≤ cDen k := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  simp only [cDen]
  nlinarith [mul_nonneg hk hk, mul_nonneg (mul_nonneg hk hk) hk,
    mul_nonneg (mul_nonneg (mul_nonneg hk hk) hk) hk]

/-- A crude but sufficient growth bound: `c k ≤ 2 · 4 ^ k`. -/
theorem c_le (k : ℕ) : c k ≤ 2 * 4 ^ k := by
  have hD : (0 : ℝ) < cDen k := cDen_pos k
  have h72 : (72 : ℝ) ≤ cDen k := seventyTwo_le_cDen k
  have hpow : (2 : ℝ) ^ (2 * k + 4) = 16 * 4 ^ k := by
    rw [pow_add, pow_mul]
    norm_num
    ring
  rw [c, hpow, div_le_iff₀ hD]
  have h4 : (0 : ℝ) < 4 ^ k := by positivity
  nlinarith [h4, h72]

/-- The key monotonicity step: for `y ≤ 1/4` one has `c (k+1) * y ≤ c k`.  This is where the
radius of convergence `1/4` of (22) enters. -/
theorem c_succ_mul_le (k : ℕ) {y : ℝ} (hy : y ≤ 1 / 4) : c (k + 1) * y ≤ c k := by
  have hD : (0 : ℝ) < cDen k := cDen_pos k
  have hD' : (0 : ℝ) < cDen (k + 1) := cDen_pos (k + 1)
  have hmono : cDen k ≤ cDen (k + 1) := cDen_le_succ k
  have hA : (0 : ℝ) < 9 * 2 ^ (2 * k + 4) := by positivity
  have hpow : (2 : ℝ) ^ (2 * (k + 1) + 4) = 4 * 2 ^ (2 * k + 4) := by
    rw [show 2 * (k + 1) + 4 = (2 * k + 4) + 2 by ring, pow_add]
    ring
  have h4y : 4 * y ≤ 1 := by linarith
  rw [c, c, hpow, div_mul_eq_mul_div, div_le_div_iff₀ hD' hD]
  calc 9 * (4 * 2 ^ (2 * k + 4)) * y * cDen k
      = (9 * 2 ^ (2 * k + 4)) * (4 * y) * cDen k := by ring
    _ ≤ (9 * 2 ^ (2 * k + 4)) * 1 * cDen k := by gcongr
    _ = (9 * 2 ^ (2 * k + 4)) * cDen k := by ring
    _ ≤ (9 * 2 ^ (2 * k + 4)) * cDen (k + 1) := by gcongr

/-- The terms `c k * y ^ k` of (22) decrease for `0 ≤ y ≤ 1/4`: the hypothesis of the
alternating series test. -/
theorem c_mul_pow_antitone {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 4) :
    Antitone fun k : ℕ => c k * y ^ k := by
  refine antitone_nat_of_succ_le fun k => ?_
  have hstep : c (k + 1) * y ≤ c k := c_succ_mul_le k hy
  have hpk : (0 : ℝ) ≤ y ^ k := pow_nonneg hy0 k
  calc c (k + 1) * y ^ (k + 1) = (c (k + 1) * y) * y ^ k := by ring
    _ ≤ c k * y ^ k := by gcongr

/-! ### The series `L` of equation (22) -/

/-- The `k`-th term `(-1)^(k+1) c k y^k` of Poitou's series (22).  The series itself starts at
`k = 1`; the value at `k = 0` is never summed. -/
noncomputable def Lterm (y : ℝ) (k : ℕ) : ℝ := (-1) ^ (k + 1) * (c k * y ^ k)

/-- Poitou's auxiliary function, equation (22):
`L(y) = (4/5) y - (144/175) y² + … + (-1)^(k+1) c k y^k + …`, the sum running over `k ≥ 1`.

The definition is written with the index shifted down by one so that it is literally of the form
`∑' j, (-1)^j * f j` required by Mathlib's alternating series API; `L_eq_tsum_Lterm` records that
this is the same as the sum of `Lterm y k` over `k ≥ 1`. -/
noncomputable def L (y : ℝ) : ℝ := ∑' j : ℕ, (-1) ^ j * (c (j + 1) * y ^ (j + 1))

theorem L_eq_tsum_Lterm (y : ℝ) : L y = ∑' j : ℕ, Lterm y (j + 1) := by
  refine tsum_congr fun j => ?_
  simp only [Lterm, pow_succ]
  ring

/-- The partial sum of (22) over `1 ≤ k < N`. -/
noncomputable def Lpartial (y : ℝ) (N : ℕ) : ℝ := ∑ k ∈ Finset.Ico 1 N, Lterm y k

@[simp] theorem Lpartial_zero (y : ℝ) : Lpartial y 0 = 0 := by simp [Lpartial]

@[simp] theorem Lpartial_one (y : ℝ) : Lpartial y 1 = 0 := by simp [Lpartial]

theorem Lpartial_succ_eq (y : ℝ) (M : ℕ) :
    Lpartial y (M + 1) = ∑ j ∈ Finset.range M, (-1) ^ j * (c (j + 1) * y ^ (j + 1)) := by
  rw [Lpartial, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show 1 + j = j + 1 from Nat.add_comm 1 j]
  simp only [Lterm, pow_succ]
  ring

/-- The shifted coefficient sequence is summable for `0 ≤ y < 1/4`, by comparison with the
geometric series of ratio `4y`. -/
theorem summable_c_mul_pow {y : ℝ} (hy0 : 0 ≤ y) (hy : y < 1 / 4) :
    Summable fun j : ℕ => c (j + 1) * y ^ (j + 1) := by
  have h4y0 : (0 : ℝ) ≤ 4 * y := by linarith
  have h4y1 : 4 * y < 1 := by linarith
  have hgeom : Summable fun j : ℕ => (8 * y) * (4 * y) ^ j :=
    (summable_geometric_of_lt_one h4y0 h4y1).mul_left _
  refine Summable.of_nonneg_of_le
    (fun j => mul_nonneg (c_nonneg _) (pow_nonneg hy0 _)) (fun j => ?_) hgeom
  have hbound : c (j + 1) ≤ 2 * 4 ^ (j + 1) := c_le (j + 1)
  have hpk : (0 : ℝ) ≤ y ^ (j + 1) := pow_nonneg hy0 (j + 1)
  calc c (j + 1) * y ^ (j + 1) ≤ (2 * 4 ^ (j + 1)) * y ^ (j + 1) := by gcongr
    _ = (8 * y) * (4 * y) ^ j := by
        rw [mul_pow, pow_succ, pow_succ]
        ring

theorem tendsto_L_partialSums {y : ℝ} (hy0 : 0 ≤ y) (hy : y < 1 / 4) :
    Tendsto (fun n => ∑ j ∈ Finset.range n, (-1) ^ j * (c (j + 1) * y ^ (j + 1))) atTop
      (𝓝 (L y)) :=
  (summable_c_mul_pow hy0 hy).tendsto_alternating_series_tsum

/-- **R4 (i): the Leibniz remainder bound for (22).**  For `0 < y < 1/4` and every `N`, the
partial sum of (22) over `1 ≤ k < N` differs from `L y` by at most the first omitted
coefficient, `c N * y ^ N`. -/
theorem abs_L_sub_Lpartial_le {y : ℝ} (hy0 : 0 < y) (hy : y < 1 / 4) (N : ℕ) :
    |L y - Lpartial y N| ≤ c N * y ^ N := by
  have hy0' : (0 : ℝ) ≤ y := hy0.le
  have hy4 : y ≤ 1 / 4 := hy.le
  have hanti : Antitone fun j : ℕ => c (j + 1) * y ^ (j + 1) := by
    intro a b hab
    exact c_mul_pow_antitone hy0' hy4 (by lia : a + 1 ≤ b + 1)
  have hmain : ∀ M : ℕ, |L y - Lpartial y (M + 1)| ≤ c (M + 1) * y ^ (M + 1) := by
    intro M
    rw [Lpartial_succ_eq]
    exact alternating_series_error_bound _ hanti (summable_c_mul_pow hy0' hy) M
  match N with
  | 0 =>
      have h1 := hmain 0
      rw [Lpartial_one] at h1
      rw [Lpartial_zero]
      refine h1.trans ?_
      simpa using c_mul_pow_antitone hy0' hy4 (by lia : 0 ≤ 1)
  | (M + 1) => exact hmain M

/-- `L` is nonnegative on the disc of convergence: the empty partial sum is a lower bound. -/
theorem L_nonneg {y : ℝ} (hy0 : 0 ≤ y) (hy : y < 1 / 4) : 0 ≤ L y := by
  have hanti : Antitone fun j : ℕ => c (j + 1) * y ^ (j + 1) := by
    intro a b hab
    exact c_mul_pow_antitone hy0 hy.le (by lia : a + 1 ≤ b + 1)
  have := hanti.alternating_series_le_tendsto (tendsto_L_partialSums hy0 hy) 0
  simpa using this

/-- The first-order upper bound `L y ≤ (4/5) y`, the case `N = 1` of the Leibniz bound. -/
theorem L_le {y : ℝ} (hy0 : 0 < y) (hy : y < 1 / 4) : L y ≤ 4 / 5 * y := by
  have h := abs_L_sub_Lpartial_le hy0 hy 1
  rw [Lpartial_one, c_one] at h
  have := (abs_le.mp h).2
  simpa using this

/-- The closed form of equation (23), valid for positive `y` outside the disc of convergence of
(22).  No statement in this file uses it; it is transcribed for the later evaluation packet. -/
noncomputable def Lclosed (y : ℝ) : ℝ :=
  -3 / (20 * y ^ 2) + 33 / (10 * y) + 2
    + (3 / (80 * y ^ 3) + 3 / (4 * y ^ 2)) * Real.log (1 + 4 * y)
    - (3 / y + 12 / 5) * (Real.arctan (2 * Real.sqrt y) / Real.sqrt y)

/-! ### Reciprocal cubes of the odd integers -/

/-- `(2m+1)⁻³`, the coefficient sequence of `λ(3)` in equation (17). -/
noncomputable def oddCube (m : ℕ) : ℝ := ((2 * m + 1 : ℝ) ^ 3)⁻¹

theorem oddCube_nonneg (m : ℕ) : 0 ≤ oddCube m := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  unfold oddCube
  positivity

theorem oddCube_shift1 (j : ℕ) : oddCube (j + 1) = 1 / (1 + 2 * (j : ℝ) + 2) ^ 3 := by
  have h : (2 * ((j + 1 : ℕ) : ℝ) + 1) = 1 + 2 * (j : ℝ) + 2 := by push_cast; ring
  rw [oddCube, h, one_div]

theorem oddCube_shift3 (j : ℕ) : oddCube (j + 3) = 1 / (5 + 2 * (j : ℝ) + 2) ^ 3 := by
  have h : (2 * ((j + 3 : ℕ) : ℝ) + 1) = 5 + 2 * (j : ℝ) + 2 := by push_cast; ring
  rw [oddCube, h, one_div]

/-- Telescoping bound: `∑_{j<n} 1/(a+2j+2)³ ≤ 1/(4a(a+2)) - 1/(4(a+2n)(a+2n+2))`, valid for
`a ≥ 1`.  The proof uses `(a+2j)(a+2j+4) ≤ (a+2j+2)²`, so that
`1/(a+2j+2)³ ≤ 1/((a+2j)(a+2j+2)(a+2j+4))`, which telescopes. -/
theorem sum_range_inv_cube_le {a : ℝ} (ha : 1 ≤ a) (n : ℕ) :
    ∑ j ∈ Finset.range n, (1 : ℝ) / (a + 2 * j + 2) ^ 3
      ≤ 1 / (4 * a * (a + 2)) - 1 / (4 * (a + 2 * n) * (a + 2 * n + 2)) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have ha0 : (0 : ℝ) < a := by linarith
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hb : (0 : ℝ) < a + 2 * n := by linarith
      have hb2 : (0 : ℝ) < a + 2 * n + 2 := by linarith
      have hb4 : (0 : ℝ) < a + 2 * n + 4 := by linarith
      have hstep : (1 : ℝ) / (a + 2 * n + 2) ^ 3
          ≤ 1 / (4 * (a + 2 * n) * (a + 2 * n + 2))
            - 1 / (4 * (a + 2 * n + 2) * (a + 2 * n + 4)) := by
        have hrhs : 1 / (4 * (a + 2 * n) * (a + 2 * n + 2))
            - 1 / (4 * (a + 2 * n + 2) * (a + 2 * n + 4))
            = 1 / ((a + 2 * n) * (a + 2 * n + 2) * (a + 2 * n + 4)) := by
          field_simp
          ring
        rw [hrhs]
        apply one_div_le_one_div_of_le
        · positivity
        · nlinarith [hb.le, hb2.le, hb4.le]
      rw [Finset.sum_range_succ]
      push_cast
      calc (∑ j ∈ Finset.range n, (1 : ℝ) / (a + 2 * j + 2) ^ 3)
              + 1 / (a + 2 * (n : ℝ) + 2) ^ 3
          ≤ (1 / (4 * a * (a + 2)) - 1 / (4 * (a + 2 * n) * (a + 2 * n + 2)))
              + (1 / (4 * (a + 2 * n) * (a + 2 * n + 2))
                  - 1 / (4 * (a + 2 * n + 2) * (a + 2 * n + 4))) := by
            gcongr
        _ = 1 / (4 * a * (a + 2)) - 1 / (4 * (a + 2 * n + 2) * (a + 2 * n + 4)) := by ring
        _ = 1 / (4 * a * (a + 2))
              - 1 / (4 * (a + 2 * ((n : ℝ) + 1)) * (a + 2 * ((n : ℝ) + 1) + 2)) := by ring

/-- `∑_{j<n} (2j+3)⁻³ ≤ 1/12`, the `a = 1` instance of the telescoping bound. -/
theorem sum_range_oddCube_shift_le (n : ℕ) :
    ∑ j ∈ Finset.range n, oddCube (j + 1) ≤ 1 / 12 := by
  have h := sum_range_inv_cube_le (a := 1) le_rfl n
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.range n) => oddCube_shift1 j]
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hp : (0 : ℝ) ≤ 1 / (4 * (1 + 2 * (n : ℝ)) * (1 + 2 * (n : ℝ) + 2)) := by positivity
  have hv : (1 : ℝ) / (4 * 1 * (1 + 2)) = 1 / 12 := by norm_num
  linarith

/-- `∑_{j<n} (2j+7)⁻³ ≤ 1/140`, the `a = 5` instance of the telescoping bound.  Poitou's constant
`λ(3) - 1 - 3⁻³ - 5⁻³ = 0.006762754…` is thereby bounded by `1/140 = 0.0071428…`. -/
theorem sum_range_oddCube_tail_le (n : ℕ) :
    ∑ j ∈ Finset.range n, oddCube (j + 3) ≤ 1 / 140 := by
  have h := sum_range_inv_cube_le (a := 5) (by norm_num) n
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.range n) => oddCube_shift3 j]
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hp : (0 : ℝ) ≤ 1 / (4 * (5 + 2 * (n : ℝ)) * (5 + 2 * (n : ℝ) + 2)) := by positivity
  have hv : (1 : ℝ) / (4 * 5 * (5 + 2)) = 1 / 140 := by norm_num
  linarith

theorem oddCube_zero : oddCube 0 = 1 := by norm_num [oddCube]

/-- `∑_{m<n} (2m+1)⁻³ ≤ 13/12`; the true value of `λ(3)` is `1.0517997…`. -/
theorem sum_range_oddCube_le (n : ℕ) : ∑ m ∈ Finset.range n, oddCube m ≤ 13 / 12 := by
  match n with
  | 0 => norm_num
  | (M + 1) =>
      rw [Finset.sum_range_succ', oddCube_zero]
      have h := sum_range_oddCube_shift_le M
      linarith

theorem summable_oddCube : Summable oddCube :=
  summable_of_sum_range_le (c := 13 / 12) oddCube_nonneg sum_range_oddCube_le

/-! ### `λ` of equation (17) and `L₁` of equation (24) -/

/-- `λ(k) = 1 + 3^(-k) + 5^(-k) + …`, Poitou's equation (17).  Classically
`λ(k) = (1 - 2^(-k)) ζ(k)`; the `tsum` over the odd integers is the form used here. -/
noncomputable def lambdaOdd (k : ℕ) : ℝ := ∑' m : ℕ, ((2 * m + 1 : ℝ) ^ k)⁻¹

theorem lambdaOdd_three : lambdaOdd 3 = ∑' m : ℕ, oddCube m := rfl

/-- Poitou's constant in the first line of (25) is bounded by `1/140`:
`λ(3) - 1 - 3⁻³ - 5⁻³ ≤ 1/140`.  (The manuscript's value is `0.006762754…`.) -/
theorem lambdaOdd_three_tail_le :
    lambdaOdd 3 - 1 - (3 : ℝ)⁻¹ ^ 3 - (5 : ℝ)⁻¹ ^ 3 ≤ 1 / 140 := by
  have hsplit := summable_oddCube.sum_add_tsum_nat_add 3
  have htail : ∑' m : ℕ, oddCube (m + 3) ≤ 1 / 140 :=
    Real.tsum_le_of_sum_range_le (fun m => oddCube_nonneg (m + 3)) sum_range_oddCube_tail_le
  have hhead : ∑ m ∈ Finset.range 3, oddCube m = 1 + (3 : ℝ)⁻¹ ^ 3 + (5 : ℝ)⁻¹ ^ 3 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    norm_num [oddCube]
  rw [lambdaOdd_three, ← hsplit, hhead]
  linarith

/-- The `m`-th term `(2m+1)⁻¹ L(y/(2m+1)²)` of Poitou's equation (24) at `r₁ = 0`. -/
noncomputable def L1term (y : ℝ) (m : ℕ) : ℝ :=
  ((2 * m + 1 : ℝ))⁻¹ * L (y / (2 * m + 1) ^ 2)

/-- Poitou's `L₁`, equation (24) specialized to the totally imaginary case `r₁ = 0`:
`L₁(y) = L(y) + (1/3) L(y/3²) + (1/5) L(y/5²) + …`. -/
noncomputable def L1 (y : ℝ) : ℝ := ∑' m : ℕ, L1term y m

theorem L1term_zero (y : ℝ) : L1term y 0 = L y := by norm_num [L1term]

theorem L1term_one (y : ℝ) : L1term y 1 = 1 / 3 * L (y / 9) := by norm_num [L1term]

theorem L1term_two (y : ℝ) : L1term y 2 = 1 / 5 * L (y / 25) := by norm_num [L1term]

theorem L1term_nonneg {y : ℝ} (hy0 : 0 < y) (hy : y < 1 / 4) (m : ℕ) : 0 ≤ L1term y m := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hd2 : (1 : ℝ) ≤ (2 * (m : ℝ) + 1) ^ 2 := by nlinarith
  have hz0 : 0 < y / (2 * (m : ℝ) + 1) ^ 2 := by positivity
  have hzy : y / (2 * (m : ℝ) + 1) ^ 2 ≤ y := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hz4 : y / (2 * (m : ℝ) + 1) ^ 2 < 1 / 4 := lt_of_le_of_lt hzy hy
  exact mul_nonneg (by positivity) (L_nonneg hz0.le hz4)

/-- Each term of (24) is at most `(4/5) y (2m+1)⁻³`, from the first-order bound on `L`. -/
theorem L1term_le {y : ℝ} (hy0 : 0 < y) (hy : y < 1 / 4) (m : ℕ) :
    L1term y m ≤ 4 / 5 * y * oddCube m := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hd : (0 : ℝ) < 2 * (m : ℝ) + 1 := by linarith
  have hd2 : (1 : ℝ) ≤ (2 * (m : ℝ) + 1) ^ 2 := by nlinarith
  have hz0 : 0 < y / (2 * (m : ℝ) + 1) ^ 2 := by positivity
  have hzy : y / (2 * (m : ℝ) + 1) ^ 2 ≤ y := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hz4 : y / (2 * (m : ℝ) + 1) ^ 2 < 1 / 4 := lt_of_le_of_lt hzy hy
  have hL : L (y / (2 * (m : ℝ) + 1) ^ 2) ≤ 4 / 5 * (y / (2 * (m : ℝ) + 1) ^ 2) :=
    L_le hz0 hz4
  have hinv : (0 : ℝ) ≤ ((2 * (m : ℝ) + 1))⁻¹ := by positivity
  calc L1term y m ≤ ((2 * (m : ℝ) + 1))⁻¹ * (4 / 5 * (y / (2 * (m : ℝ) + 1) ^ 2)) :=
        mul_le_mul_of_nonneg_left hL hinv
    _ = 4 / 5 * y * oddCube m := by
        rw [oddCube]
        field_simp

/-- **R4 (ii): the tail of `L₁` after the three terms Poitou keeps.**  For `0 < y < 1/4`,
`∑_{m ≥ 3} (2m+1)⁻¹ L(y/(2m+1)²) ≤ y / 175`.

This is the fully certified counterpart of the first line of Poitou's equation (25), where the
constant is `(4/5)(λ(3) - 1 - 3⁻³ - 5⁻³) = (4/5)(0.006762754…) = 0.005410…`.  Here the constant
is `(4/5)(1/140) = 1/175 = 0.005714…`: weaker than Poitou's, but proved, and still `O(y)` with
an explicit rational constant, which is all that the downstream arithmetic packet needs. -/
theorem L1_tail_le {y : ℝ} (hy0 : 0 < y) (hy : y < 1 / 4) :
    ∑' m : ℕ, L1term y (m + 3) ≤ y / 175 := by
  refine Real.tsum_le_of_sum_range_le (fun m => L1term_nonneg hy0 hy (m + 3)) (fun n => ?_)
  have hy45 : (0 : ℝ) ≤ 4 / 5 * y := by linarith
  calc ∑ m ∈ Finset.range n, L1term y (m + 3)
      ≤ ∑ m ∈ Finset.range n, 4 / 5 * y * oddCube (m + 3) :=
        Finset.sum_le_sum fun m _ => L1term_le hy0 hy (m + 3)
    _ = 4 / 5 * y * ∑ m ∈ Finset.range n, oddCube (m + 3) := by rw [Finset.mul_sum]
    _ ≤ 4 / 5 * y * (1 / 140) := by
        gcongr
        exact sum_range_oddCube_tail_le n
    _ = y / 175 := by ring

/-- The series (24) converges for `0 < y < 1/4`. -/
theorem L1_summable {y : ℝ} (hy0 : 0 < y) (hy : y < 1 / 4) : Summable (L1term y) := by
  refine summable_of_sum_range_le (c := 4 / 5 * y * (13 / 12))
    (fun m => L1term_nonneg hy0 hy m) (fun n => ?_)
  have hy45 : (0 : ℝ) ≤ 4 / 5 * y := by linarith
  calc ∑ m ∈ Finset.range n, L1term y m
      ≤ ∑ m ∈ Finset.range n, 4 / 5 * y * oddCube m :=
        Finset.sum_le_sum fun m _ => L1term_le hy0 hy m
    _ = 4 / 5 * y * ∑ m ∈ Finset.range n, oddCube m := by rw [Finset.mul_sum]
    _ ≤ 4 / 5 * y * (13 / 12) := by
        gcongr
        exact sum_range_oddCube_le n

/-- `L₁` splits as the three terms Poitou keeps in (25) plus the tail bounded by `L1_tail_le`. -/
theorem L1_eq_head_add_tail {y : ℝ} (hy0 : 0 < y) (hy : y < 1 / 4) :
    L1 y = (L y + 1 / 3 * L (y / 9) + 1 / 5 * L (y / 25)) + ∑' m : ℕ, L1term y (m + 3) := by
  have hsplit := (L1_summable hy0 hy).sum_add_tsum_nat_add 3
  rw [L1, ← hsplit]
  congr 1
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, L1term_zero, L1term_one, L1term_two]
  ring

/-- The consequence used downstream: `L₁(y)` is at most the three Poitou head terms plus `y/175`.
Substituted into equation (26) this gives, for a totally imaginary field of degree `n`,
`(1/n) log|d| ≥ γ + log(4π) - 12π/(5n√y) - (L(y) + L(y/9)/3 + L(y/25)/5) - y/175`. -/
theorem L1_le_head_add {y : ℝ} (hy0 : 0 < y) (hy : y < 1 / 4) :
    L1 y ≤ (L y + 1 / 3 * L (y / 9) + 1 / 5 * L (y / 25)) + y / 175 := by
  rw [L1_eq_head_add_tail hy0 hy]
  have := L1_tail_le hy0 hy
  linarith

end Odlyzko.Poitou
