/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.Odlyzko.Interval.Rat
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Certified intervals for transcendental constants

Rational interval evaluators for the constants used in the Odlyzko calculation.  The logarithm
evaluator applies the Taylor remainder bound for `log (1 - x)` after the atanh substitution
`x = (q - 1) / (q + 1)`, so it works for every positive rational `q`.  The arctangent evaluator
uses alternating partial sums on `[0, 1)`; its natural-number argument controls the enclosure
width.  The Euler–Mascheroni evaluator combines those logarithm bounds with Mathlib's monotone
harmonic bounds.  Pi uses Mathlib's certified decimal tables, selectable through 20 digits.
-/

@[expose] public section

namespace Odlyzko.Interval

open Finset

namespace Constants

/-- The coarse enclosure of Euler's constant provided directly by Mathlib. -/
def eulerGammaCoarseEnclosure : RatIvl := ⟨1 / 2, 2 / 3, by norm_num⟩

theorem eulerGamma_mem_coarse :
    Real.eulerMascheroniConstant ∈ (eulerGammaCoarseEnclosure : Set ℝ) := by
  constructor
  · simpa [eulerGammaCoarseEnclosure] using Real.one_half_lt_eulerMascheroniConstant.le
  · simpa [eulerGammaCoarseEnclosure] using Real.eulerMascheroniConstant_lt_two_thirds.le

/-- The ten-decimal enclosure of `log 2` provided directly by Mathlib. -/
def logTwoEnclosure : RatIvl := ⟨0.6931471803, 0.6931471808, by norm_num⟩

theorem log_two_mem : Real.log 2 ∈ (logTwoEnclosure : Set ℝ) := by
  exact ⟨Real.log_two_gt_d9.le, Real.log_two_lt_d9.le⟩

/-- The rational Taylor polynomial `Σ_{i<n} x^(i+1)/(i+1)`. -/
def logOneMinusSum (x : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ range n, x ^ (i + 1) / (i + 1)

/-- The explicit remainder bound for the Taylor polynomial of `log (1 - x)`. -/
def logOneMinusError (x : ℚ) (n : ℕ) : ℚ :=
  |x| ^ (n + 1) / (1 - |x|)

/-- Certified enclosure of `log (1 - x)` for rational `|x| < 1`. -/
def logOneMinusEnclosure (x : ℚ) (n : ℕ) (hx : |x| < 1) : RatIvl :=
  ⟨-logOneMinusSum x n - logOneMinusError x n,
    -logOneMinusSum x n + logOneMinusError x n, by
      have he : 0 ≤ logOneMinusError x n := by
        exact div_nonneg (pow_nonneg (abs_nonneg x) _) (sub_nonneg.mpr hx.le)
      linarith⟩

theorem logOneMinus_mem (x : ℚ) (n : ℕ) (hx : |x| < 1) :
    Real.log (1 - (x : ℝ)) ∈ (logOneMinusEnclosure x n hx : Set ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (x : ℝ)) (by exact_mod_cast hx) n
  have hsum : ((logOneMinusSum x n : ℚ) : ℝ) =
      ∑ i ∈ range n, (x : ℝ) ^ (i + 1) / (i + 1) := by
    simp [logOneMinusSum]
  have herr : ((logOneMinusError x n : ℚ) : ℝ) =
      |(x : ℝ)| ^ (n + 1) / (1 - |(x : ℝ)|) := by
    simp [logOneMinusError]
  rw [← hsum, ← herr] at h
  rcases abs_le.mp h with ⟨hlo, hhi⟩
  constructor <;> change (_ : ℝ) ≤ _ <;>
    simp only [logOneMinusEnclosure, Rat.cast_sub, Rat.cast_neg, Rat.cast_add] <;> linarith

/-- The atanh substitution, which lies in `(-1, 1)` for every positive rational input. -/
def logArgument (q : ℚ) : ℚ := (q - 1) / (q + 1)

theorem abs_logArgument_lt_one (q : ℚ) (hq : 0 < q) : |logArgument q| < 1 := by
  rw [abs_lt]
  have hden : 0 < q + 1 := by linarith
  constructor
  · unfold logArgument
    rw [lt_div_iff₀ hden]
    linarith
  · unfold logArgument
    rw [div_lt_iff₀ hden]
    linarith

/-- A tunable enclosure of `log q` for every positive rational `q`. -/
def logEnclosure (q : ℚ) (n : ℕ) (hq : 0 < q) : RatIvl :=
  let x := logArgument q
  RatIvl.sub (logOneMinusEnclosure (-x) n (by simpa using abs_logArgument_lt_one q hq))
    (logOneMinusEnclosure x n (abs_logArgument_lt_one q hq))

theorem log_mem (q : ℚ) (n : ℕ) (hq : 0 < q) :
    Real.log (q : ℝ) ∈ (logEnclosure q n hq : Set ℝ) := by
  let x := logArgument q
  have hx : |x| < 1 := abs_logArgument_lt_one q hq
  have hpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hone_sub : (1 : ℝ) - (x : ℝ) ≠ 0 := by
    have : (x : ℝ) < 1 := (abs_lt.mp (by exact_mod_cast hx)).2
    linarith
  have hratio : ((1 : ℝ) + (x : ℝ)) / (1 - (x : ℝ)) = q := by
    dsimp [x, logArgument]
    norm_num
    field_simp
    ring
  have hlog : Real.log (q : ℝ) =
      Real.log (1 - ((-x : ℚ) : ℝ)) - Real.log (1 - (x : ℝ)) := by
    have hxlower : (-1 : ℝ) < x := (abs_lt.mp (by exact_mod_cast hx)).1
    have hnum : (1 : ℝ) - ((-x : ℚ) : ℝ) ≠ 0 := by
      norm_num
      linarith
    rw [← Real.log_div hnum hone_sub]
    norm_num
    exact congrArg Real.log hratio.symm
  rw [hlog]
  exact RatIvl.mem_sub
    (logOneMinus_mem (-x) n (by simpa using hx)) (logOneMinus_mem x n hx)

/-- Certified enclosure of Euler's constant at harmonic index `k` and logarithm precision `n`. -/
def eulerGammaEnclosure (k n : ℕ) (hk : 0 < k) : RatIvl :=
  let lowerLog := logEnclosure (k + 1) n (by positivity)
  let upperLog := logEnclosure k n (by exact_mod_cast hk)
  ⟨harmonic k - lowerLog.hi, harmonic k - upperLog.lo, by
    apply (Rat.cast_le (K := ℝ)).mp
    have hl := log_mem (k + 1) n (by positivity)
    have hu := log_mem k n (by exact_mod_cast hk)
    rw [RatIvl.mem_coe] at hl hu
    have hcastSucc : (((k : ℚ) + 1 : ℚ) : ℝ) = (k : ℝ) + 1 := by norm_num
    have hcast : (((k : ℚ) : ℚ) : ℝ) = (k : ℝ) := by norm_num
    rw [hcastSucc] at hl
    rw [hcast] at hu
    have hgammaLower := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant k
    have hgammaUpper := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' k
    simp only [Real.eulerMascheroniSeq] at hgammaLower
    simp only [Real.eulerMascheroniSeq', hk.ne', ite_false] at hgammaUpper
    change ((harmonic k - lowerLog.hi : ℚ) : ℝ) ≤
      ((harmonic k - upperLog.lo : ℚ) : ℝ)
    dsimp only [lowerLog, upperLog] at hl hu ⊢
    simp only [Rat.cast_sub] at ⊢
    linarith [hl.2, hu.1, hgammaLower, hgammaUpper]⟩

theorem eulerGamma_mem (k n : ℕ) (hk : 0 < k) :
    Real.eulerMascheroniConstant ∈ (eulerGammaEnclosure k n hk : Set ℝ) := by
  let lowerLog := logEnclosure (k + 1) n (by positivity)
  let upperLog := logEnclosure k n (by exact_mod_cast hk)
  have hl := log_mem (k + 1) n (by positivity)
  have hu := log_mem k n (by exact_mod_cast hk)
  rw [RatIvl.mem_coe] at hl hu
  have hcastSucc : (((k : ℚ) + 1 : ℚ) : ℝ) = (k : ℝ) + 1 := by norm_num
  have hcast : (((k : ℚ) : ℚ) : ℝ) = (k : ℝ) := by norm_num
  rw [hcastSucc] at hl
  rw [hcast] at hu
  have hgammaLower := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant k
  have hgammaUpper := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' k
  simp only [Real.eulerMascheroniSeq] at hgammaLower
  simp only [Real.eulerMascheroniSeq', hk.ne', ite_false] at hgammaUpper
  constructor
  · change ((eulerGammaEnclosure k n hk).lo : ℝ) ≤ Real.eulerMascheroniConstant
    simp only [eulerGammaEnclosure, Rat.cast_sub]
    linarith [hl.2, hgammaLower]
  · change Real.eulerMascheroniConstant ≤ ((eulerGammaEnclosure k n hk).hi : ℝ)
    simp only [eulerGammaEnclosure, Rat.cast_sub]
    linarith [hu.1, hgammaUpper]

/-- Supported decimal precision for the table-based pi enclosure. -/
inductive PiPrecision
  | digits2
  | digits4
  | digits6
  | digits20
  deriving DecidableEq

/-- Certified Mathlib table enclosure of pi, selectable through 20 decimal digits. -/
def piEnclosure : PiPrecision → RatIvl
  | .digits2 => ⟨3.14, 3.15, by norm_num⟩
  | .digits4 => ⟨3.1415, 3.1416, by norm_num⟩
  | .digits6 => ⟨3.141592, 3.141593, by norm_num⟩
  | .digits20 =>
      ⟨3.14159265358979323846, 3.14159265358979323847, by norm_num⟩

theorem pi_mem (precision : PiPrecision) :
    Real.pi ∈ (piEnclosure precision : Set ℝ) := by
  cases precision
  · simpa [piEnclosure] using And.intro Real.pi_gt_d2.le Real.pi_lt_d2.le
  · simpa [piEnclosure] using And.intro Real.pi_gt_d4.le Real.pi_lt_d4.le
  · simpa [piEnclosure] using And.intro Real.pi_gt_d6.le Real.pi_lt_d6.le
  · simpa [piEnclosure] using And.intro Real.pi_gt_d20.le Real.pi_lt_d20.le

/-- The `n`-term rational Taylor polynomial for arctangent. -/
def arctanPartial (q : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ range n, (-1) ^ i * q ^ (2 * i + 1) / (2 * i + 1)

/-- Alternating lower and upper sums for `arctan q`, with a tunable number of term pairs. -/
def arctanSmallEnclosure (q : ℚ) (n : ℕ) (hq : 0 ≤ q) : RatIvl :=
  ⟨arctanPartial q (2 * n), arctanPartial q (2 * n + 1), by
    rw [arctanPartial, arctanPartial, sum_range_succ]
    simp only [Even.neg_one_pow (even_two_mul n), one_mul]
    exact le_add_of_nonneg_right (div_nonneg (pow_nonneg hq _) (by positivity))⟩

theorem arctanSmall_mem (q : ℚ) (n : ℕ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Real.arctan (q : ℝ) ∈ (arctanSmallEnclosure q n hq0 : Set ℝ) := by
  let f : ℕ → ℝ := fun i ↦ (q : ℝ) ^ (2 * i + 1) / (2 * i + 1)
  have hq0' : (0 : ℝ) ≤ q := by exact_mod_cast hq0
  have hq1' : (q : ℝ) < 1 := by exact_mod_cast hq1
  have hf : Antitone f := by
    apply antitone_nat_of_succ_le
    intro i
    have hp : (q : ℝ) ^ (2 * (i + 1) + 1) ≤ (q : ℝ) ^ (2 * i + 1) := by
      exact pow_le_pow_of_le_one hq0' hq1'.le (by omega)
    apply div_le_div₀ (pow_nonneg hq0' _) hp (by positivity)
    norm_num
  have hnorm : ‖(q : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0']
    exact hq1'
  have hsum := Real.hasSum_arctan (x := (q : ℝ)) hnorm
  have ht : Filter.Tendsto
      (fun m ↦ ∑ i ∈ range m, (-1 : ℝ) ^ i * f i) Filter.atTop
        (nhds (Real.arctan (q : ℝ))) := by
    simpa [f, div_eq_mul_inv, mul_assoc] using hsum.tendsto_sum_nat
  have hlo := hf.alternating_series_le_tendsto ht n
  have hhi := hf.tendsto_le_alternating_series ht n
  constructor
  · simpa [arctanSmallEnclosure, arctanPartial, f, div_eq_mul_inv, mul_assoc] using hlo
  · simpa [arctanSmallEnclosure, arctanPartial, f, div_eq_mul_inv, mul_assoc] using hhi

/-- Scale an interval by a nonnegative rational. -/
def scaleNonneg (c : ℚ) (hc : 0 ≤ c) (I : RatIvl) : RatIvl :=
  ⟨c * I.lo, c * I.hi, mul_le_mul_of_nonneg_left I.lo_le_hi hc⟩

theorem mem_scaleNonneg {c : ℚ} (hc : 0 ≤ c) {I : RatIvl} {x : ℝ}
    (hx : x ∈ (I : Set ℝ)) : (c : ℝ) * x ∈ (scaleNonneg c hc I : Set ℝ) := by
  constructor <;> change (_ : ℝ) ≤ _
  · simpa [scaleNonneg] using mul_le_mul_of_nonneg_left hx.1 (by exact_mod_cast hc)
  · simpa [scaleNonneg] using mul_le_mul_of_nonneg_left hx.2 (by exact_mod_cast hc)

/-- Pi divided by two, retaining the selected table precision. -/
def piHalfEnclosure (precision : PiPrecision) : RatIvl :=
  scaleNonneg (1 / 2) (by norm_num) (piEnclosure precision)

theorem pi_div_two_mem (precision : PiPrecision) :
    Real.pi / 2 ∈ (piHalfEnclosure precision : Set ℝ) := by
  simpa [piHalfEnclosure, div_eq_mul_inv, mul_comm] using
    mem_scaleNonneg (c := (1 / 2 : ℚ)) (by norm_num) (pi_mem precision)

/-- Pi divided by four, used for `arctan 1`. -/
def piQuarterEnclosure (precision : PiPrecision) : RatIvl :=
  scaleNonneg (1 / 4) (by norm_num) (piEnclosure precision)

theorem pi_div_four_mem (precision : PiPrecision) :
    Real.pi / 4 ∈ (piQuarterEnclosure precision : Set ℝ) := by
  simpa [piQuarterEnclosure, div_eq_mul_inv, mul_comm] using
    mem_scaleNonneg (c := (1 / 4 : ℚ)) (by norm_num) (pi_mem precision)

/-- Reciprocal reduction for positive rational arguments larger than one. -/
def arctanLargeEnclosure (q : ℚ) (n : ℕ) (hq : 1 < q)
    (precision : PiPrecision) : RatIvl :=
  RatIvl.sub (piHalfEnclosure precision)
    (arctanSmallEnclosure q⁻¹ n (inv_nonneg.mpr (le_trans zero_le_one hq.le)))

theorem arctanLarge_mem (q : ℚ) (n : ℕ) (hq : 1 < q) (precision : PiPrecision) :
    Real.arctan (q : ℝ) ∈ (arctanLargeEnclosure q n hq precision : Set ℝ) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_trans zero_lt_one hq)
  have hinv0 : (0 : ℚ) ≤ q⁻¹ := inv_nonneg.mpr (le_trans zero_le_one hq.le)
  have hinv1 : q⁻¹ < (1 : ℚ) := inv_lt_one_of_one_lt₀ hq
  have hsmall := arctanSmall_mem q⁻¹ n hinv0 hinv1
  have hsub := RatIvl.mem_sub (pi_div_two_mem precision) hsmall
  have hid := Real.arctan_inv_of_pos hqpos
  have hcast : ((q⁻¹ : ℚ) : ℝ) = ((q : ℝ)⁻¹) := by simp
  rw [hcast, hid] at hsub
  convert hsub using 1 <;> simp [arctanLargeEnclosure]

/-- Arctangent enclosure for a nonnegative rational argument. -/
def arctanNonnegativeEnclosure (q : ℚ) (n : ℕ) (hq : 0 ≤ q)
    (precision : PiPrecision) : RatIvl :=
  if hsmall : q < 1 then
    arctanSmallEnclosure q n hq
  else if hone : q = 1 then
    piQuarterEnclosure precision
  else
    arctanLargeEnclosure q n (lt_of_le_of_ne (le_of_not_gt hsmall) (Ne.symm hone)) precision

theorem arctanNonnegative_mem (q : ℚ) (n : ℕ) (hq : 0 ≤ q)
    (precision : PiPrecision) :
    Real.arctan (q : ℝ) ∈ (arctanNonnegativeEnclosure q n hq precision : Set ℝ) := by
  by_cases hsmall : q < 1
  · simpa [arctanNonnegativeEnclosure, hsmall] using arctanSmall_mem q n hq hsmall
  by_cases hone : q = 1
  · subst q
    simpa [arctanNonnegativeEnclosure, pi_div_four_mem, Real.arctan_one]
      using pi_div_four_mem precision
  · have hlarge : 1 < q := lt_of_le_of_ne (le_of_not_gt hsmall) (Ne.symm hone)
    simpa [arctanNonnegativeEnclosure, hsmall, hone] using
      arctanLarge_mem q n hlarge precision

/-- A tunable certified enclosure of `arctan q` for every rational `q`. -/
def arctanEnclosure (q : ℚ) (n : ℕ) (precision : PiPrecision) : RatIvl :=
  if hq : 0 ≤ q then
    arctanNonnegativeEnclosure q n hq precision
  else
    RatIvl.neg (arctanNonnegativeEnclosure (-q) n (neg_nonneg.mpr (le_of_not_ge hq)) precision)

theorem arctan_mem (q : ℚ) (n : ℕ) (precision : PiPrecision) :
    Real.arctan (q : ℝ) ∈ (arctanEnclosure q n precision : Set ℝ) := by
  by_cases hq : 0 ≤ q
  · simpa [arctanEnclosure, hq] using arctanNonnegative_mem q n hq precision
  · have hneg : q ≤ 0 := le_of_not_ge hq
    have hpos := arctanNonnegative_mem (-q) n (neg_nonneg.mpr hneg) precision
    have hmem := RatIvl.mem_neg hpos
    rw [show (((-q : ℚ) : ℝ)) = -(q : ℝ) by norm_num, Real.arctan_neg, neg_neg] at hmem
    simpa [arctanEnclosure, hq] using hmem

end Constants

end Odlyzko.Interval
