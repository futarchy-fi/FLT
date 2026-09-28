/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FontaineQuotientValuation
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.RingTheory.DividedPowers.Padic

/-!
# Divided powers on Fontaine valuation ideals

For a finite extension of `ℚ_[3]`, the valuation ideal with cutoff `t ≥ 1/2`
has divided powers given by `xⁿ/n!`. Legendre's factorial bound gives the
stronger valuation estimate `n*t - (n-1)/2`. If `t > 1/2`, these values decay
geometrically to zero, uniformly in the element of the ideal.

This supplies scalar divided powers and their decay. It does not construct
the divided-power filtration of a presentation or lift algebra homomorphisms.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable (E : Type*) [Field E] [Algebra ℚ_[3] E] [Algebra ℤ_[3] E]
  [IsScalarTower ℤ_[3] ℚ_[3] E] [FiniteDimensional ℚ_[3] E]

omit [Algebra ℤ_[3] E] [IsScalarTower ℤ_[3] ℚ_[3] E] [FiniteDimensional ℚ_[3] E] in
/-- The norm of a nonzero natural number in a three-adic extension is determined
by its three-adic valuation. -/
theorem spectralNorm_natCast_eq_rpow (n : ℕ) (hn : n ≠ 0) :
    spectralNorm ℚ_[3] E (n : E) = (3 : ℝ) ^ (-(padicValNat 3 n : ℝ)) := by
  rw [← map_natCast (algebraMap ℚ_[3] E) n, spectralNorm_extends]
  rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hn), Padic.valuation_natCast]
  simp only [← Real.rpow_intCast, Int.cast_neg, Int.cast_natCast, Nat.cast_ofNat]

/-- Legendre’s factorial bound controls divided powers with the sharp
linear lower bound `n*t - (n-1)/2` on their valuation. -/
theorem spectralNorm_divided_power_le {t : ℚ} {x : ThreeAdicIntegers E}
    (hx : x ∈ threeAdicValuationIdeal E t) {n : ℕ} (hn : n ≠ 0) :
    spectralNorm ℚ_[3] E ((x : E) ^ n / (n.factorial : E)) ≤
      (3 : ℝ) ^ (-(((n : ℚ) * t - ((n : ℚ) - 1) / 2 : ℚ) : ℝ)) := by
  let := spectralNorm.nontriviallyNormedField ℚ_[3] E
  change ‖(x : E) ^ n / (n.factorial : E)‖ ≤ _
  change ‖(x : E)‖ ≤ (3 : ℝ) ^ (-(t : ℝ)) at hx
  have hfac : ‖(n.factorial : E)‖ = (3 : ℝ) ^ (-(padicValNat 3 n.factorial : ℝ)) :=
    spectralNorm_natCast_eq_rpow E n.factorial n.factorial_ne_zero
  have hvn : 2 * padicValNat 3 n.factorial + 1 ≤ n := by
    have hh := sub_one_mul_padicValNat_factorial_lt_of_ne_zero 3 hn
    omega
  have hv : (padicValNat 3 n.factorial : ℝ) ≤ ((n : ℝ) - 1) / 2 := by
    have hh : (2 : ℝ) * padicValNat 3 n.factorial + 1 ≤ n := by exact_mod_cast hvn
    linarith
  rw [norm_div, norm_pow, hfac]
  calc
    _ ≤ ((3 : ℝ) ^ (-(t : ℝ))) ^ n /
        (3 : ℝ) ^ (-(padicValNat 3 n.factorial : ℝ)) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hx n) (by positivity)
    _ = (3 : ℝ) ^ ((padicValNat 3 n.factorial : ℝ) - n * (t : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
        ← Real.rpow_sub (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith

/-- Every divided power of an element of a valuation ideal of cutoff at
least one half is integral; every positive divided power stays in the ideal. -/
theorem exists_integral_divided_power {t : ℚ} (ht : 1 / 2 ≤ t)
    (n : ℕ) {x : ThreeAdicIntegers E} (hx : x ∈ threeAdicValuationIdeal E t) :
    ∃ y : ThreeAdicIntegers E,
      (n ≠ 0 → y ∈ threeAdicValuationIdeal E t) ∧
      (y : E) = (x : E) ^ n / (n.factorial : E) := by
  by_cases hn : n = 0
  · subst n
    exact ⟨1, by simp⟩
  have hbound := spectralNorm_divided_power_le E hx hn
  have hnorm : spectralNorm ℚ_[3] E ((x : E) ^ n / (n.factorial : E)) ≤
      (3 : ℝ) ^ (-(t : ℝ)) := by
    apply hbound.trans
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have ht' : (1 / 2 : ℝ) ≤ (t : ℝ) := by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using (Rat.cast_le (K := ℝ)).mpr ht
    push_cast
    nlinarith
  have hnorm1 : spectralNorm ℚ_[3] E ((x : E) ^ n / (n.factorial : E)) ≤ 1 :=
    hnorm.trans (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by have ht' : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (show (0 : ℚ) ≤ t by linarith)
          linarith))
  exact ⟨⟨(x : E) ^ n / (n.factorial : E),
    (isIntegral_iff_spectralNorm_le_one E _).mpr hnorm1⟩, fun _ ↦ hnorm, rfl⟩

/-- The divided-power structure on a finite three-adic extension’s
valuation ideal with cutoff at least one half. -/
def threeAdicValuationDividedPowers {t : ℚ} (ht : 1 / 2 ≤ t) :
    DividedPowers (threeAdicValuationIdeal E t) := by
  classical
  let : CharZero E := Algebra.charZero_of_charZero ℚ_[3] E
  let f := (ThreeAdicIntegers E).val.toRingHom
  apply DividedPowers.ofInjective (threeAdicValuationIdeal E t)
    ((threeAdicValuationIdeal E t).map f) f Subtype.val_injective
    (DividedPowers.RatAlgebra.dividedPowers _) rfl
  intro n x hx
  obtain ⟨y, hy, he⟩ := exists_integral_divided_power E ht n hx
  refine ⟨y, hy, ?_⟩
  rw [DividedPowers.RatAlgebra.dpow_apply, ite_eq_left (Ideal.mem_map_of_mem f hx)]
  change (y : E) = _
  rw [he, Ring.inverse_eq_inv']
  exact div_eq_inv_mul _ _

/-- The divided powers on a Fontaine valuation ideal have the expected
formula in the fraction field. -/
theorem coe_threeAdicValuationDividedPowers {t : ℚ} (ht : 1 / 2 ≤ t)
    (n : ℕ) {x : ThreeAdicIntegers E} (hx : x ∈ threeAdicValuationIdeal E t) :
    ((threeAdicValuationDividedPowers E ht).dpow n x : E) =
      (x : E) ^ n / (n.factorial : E) := by
  let : CharZero E := Algebra.charZero_of_charZero ℚ_[3] E
  have hh := (threeAdicValuationDividedPowers E ht).factorial_mul_dpow_eq_pow (n := n) hx
  have he := congrArg (ThreeAdicIntegers E).val hh
  simp only [map_mul, map_natCast, map_pow] at he
  apply (eq_div_iff (show (n.factorial : E) ≠ 0 from Nat.cast_ne_zero.mpr n.factorial_ne_zero)).mpr
  exact (mul_comm _ _).trans he

/-- A geometric bound for divided powers, uniform in the element of the
valuation ideal, including the zeroth divided power. -/
theorem spectralNorm_divided_power_le_geometric {t : ℚ} {x : ThreeAdicIntegers E}
    (hx : x ∈ threeAdicValuationIdeal E t) (n : ℕ) :
    spectralNorm ℚ_[3] E ((x : E) ^ n / (n.factorial : E)) ≤
      ((3 : ℝ) ^ (-((t : ℝ) - 1 / 2))) ^ n := by
  by_cases hn : n = 0
  · subst n
    let := spectralNorm.nontriviallyNormedField ℚ_[3] E
    change ‖(x : E) ^ 0 / (Nat.factorial 0 : E)‖ ≤ _
    simp
  apply (spectralNorm_divided_power_le E hx hn).trans
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  push_cast
  nlinarith

/-- Divided powers tend to zero when the valuation cutoff strictly
exceeds one half. -/
theorem tendsto_spectralNorm_divided_power_zero {t : ℚ} (ht : 1 / 2 < t)
    {x : ThreeAdicIntegers E} (hx : x ∈ threeAdicValuationIdeal E t) :
    Filter.Tendsto (fun n : ℕ ↦ spectralNorm ℚ_[3] E ((x : E) ^ n / (n.factorial : E)))
      Filter.atTop (nhds 0) := by
  let := spectralNorm.nontriviallyNormedField ℚ_[3] E
  have hnonneg (n : ℕ) : 0 ≤ spectralNorm ℚ_[3] E ((x : E) ^ n / (n.factorial : E)) :=
    norm_nonneg ((x : E) ^ n / (n.factorial : E))
  apply squeeze_zero hnonneg (spectralNorm_divided_power_le_geometric E hx)
  apply tendsto_pow_atTop_nhds_zero_of_lt_one (Real.rpow_nonneg (by norm_num) _)
  apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
  have ht' : (1 / 2 : ℝ) < (t : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using (Rat.cast_lt (K := ℝ)).mpr ht
  linarith

end ThreeAdicPlan
