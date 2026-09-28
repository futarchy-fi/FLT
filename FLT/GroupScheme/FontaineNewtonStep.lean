/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FontaineQuotientValuation
public import FLT.Mathlib.RingTheory.PowerBasisDifferentialBezout
public import Mathlib.Algebra.Polynomial.Identities

/-!
# Integral Newton corrections over finite three-adic extensions

The polynomial Bézout identity obtained from differential annihilation bounds
the derivative at approximate roots. This makes the Newton correction integral
and bounds its loss of precision by one.
-/

@[expose] public noncomputable section

open Polynomial

namespace ThreeAdicPlan

variable (E : Type*) [Field E] [Algebra ℚ_[3] E] [Algebra ℤ_[3] E]
  [IsScalarTower ℤ_[3] ℚ_[3] E] [FiniteDimensional ℚ_[3] E]

/-- A polynomial with integral coefficients has integral values at integral elements. -/
theorem spectralNorm_aeval_integral_le_one (f : ℤ_[3][X]) (x : ThreeAdicIntegers E) :
    spectralNorm ℚ_[3] E (aeval (x : E) f) ≤ 1 := by
  have he : aeval (x : E) f = ((aeval x f : ThreeAdicIntegers E) : E) :=
    aeval_algHom_apply (ThreeAdicIntegers E).val x f
  rw [he]
  exact (isIntegral_iff_spectralNorm_le_one E _).mp (aeval x f).property

/-- A Bézout identity with constant three bounds the derivative below once
the error has valuation strictly greater than one. -/
theorem spectralNorm_derivative_ge_of_bezout (f q r : ℤ_[3][X])
    (hbez : C (3 : ℤ_[3]) = q * f.derivative + r * f)
    (x : ThreeAdicIntegers E)
    (hx : spectralNorm ℚ_[3] E (aeval (x : E) f) < (3 : ℝ)⁻¹) :
    (3 : ℝ)⁻¹ ≤ spectralNorm ℚ_[3] E (aeval (x : E) f.derivative) := by
  let := spectralNorm.nontriviallyNormedField ℚ_[3] E
  have he := congrArg (aeval (x : E)) hbez
  simp only [map_add, map_mul, map_ofNat] at he
  have hna := isNonarchimedean_spectralNorm (K := ℚ_[3]) (L := E)
    (aeval (x : E) q * aeval (x : E) f.derivative)
    (aeval (x : E) r * aeval (x : E) f)
  change ‖aeval (x : E) q * aeval (x : E) f.derivative +
    aeval (x : E) r * aeval (x : E) f‖ ≤
    max ‖aeval (x : E) q * aeval (x : E) f.derivative‖
      ‖aeval (x : E) r * aeval (x : E) f‖ at hna
  rw [← he, norm_mul, norm_mul] at hna
  change spectralNorm ℚ_[3] E (3 : E) ≤ _ at hna
  rw [spectralNorm_three] at hna
  have hq := spectralNorm_aeval_integral_le_one E q x
  have hr := spectralNorm_aeval_integral_le_one E r x
  change ‖aeval (x : E) q‖ ≤ 1 at hq
  change ‖aeval (x : E) r‖ ≤ 1 at hr
  change ‖aeval (x : E) f‖ < (3 : ℝ)⁻¹ at hx
  apply le_of_not_gt
  intro hd
  change ‖aeval (x : E) f.derivative‖ < (3 : ℝ)⁻¹ at hd
  exact (not_lt_of_ge hna) (max_lt
    ((mul_le_mul_of_nonneg_right hq (norm_nonneg _)).trans_lt (by simpa only [one_mul] using hd))
    ((mul_le_mul_of_nonneg_right hr (norm_nonneg _)).trans_lt (by simpa only [one_mul] using hx)))

/-- For a monogenic algebra with differentials killed by three, every
approximate root of precision greater than one has derivative valuation at most one. -/
theorem _root_.PowerBasis.spectralNorm_derivative_ge_of_three_smul
    {A : Type*} [CommRing A] [Algebra ℤ_[3] A] (pb : PowerBasis ℤ_[3] A)
    (hΩ : ∀ ω : KaehlerDifferential ℤ_[3] A, (3 : ℤ_[3]) • ω = 0)
    (x : ThreeAdicIntegers E) {m : ℚ} (hm : 1 < m)
    (hx : aeval x (minpoly ℤ_[3] pb.gen) ∈ threeAdicValuationIdeal E m) :
    (3 : ℝ)⁻¹ ≤ spectralNorm ℚ_[3] E
      (aeval (x : E) (minpoly ℤ_[3] pb.gen).derivative) := by
  obtain ⟨q, r, hbez⟩ := pb.exists_minpoly_derivative_bezout 3 hΩ
  apply spectralNorm_derivative_ge_of_bezout E _ q r hbez x
  have hcut : (3 : ℝ) ^ (-(m : ℝ)) < (3 : ℝ)⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by exact_mod_cast neg_lt_neg hm)
  have he : aeval (x : E) (minpoly ℤ_[3] pb.gen) =
      ((aeval x (minpoly ℤ_[3] pb.gen) : ThreeAdicIntegers E) : E) :=
    aeval_algHom_apply (ThreeAdicIntegers E).val x _
  rw [he]
  exact hx.trans_lt hcut

/-- Division by a derivative of valuation at most one loses at most one
unit of precision. In particular the Newton correction is integral. -/
theorem exists_integral_newton_correction (f : ℤ_[3][X])
    (x : ThreeAdicIntegers E) {m : ℚ} (hm : 1 < m)
    (hx : aeval x f ∈ threeAdicValuationIdeal E m)
    (hd : (3 : ℝ)⁻¹ ≤ spectralNorm ℚ_[3] E (aeval (x : E) f.derivative)) :
    ∃ δ : ThreeAdicIntegers E, δ ∈ threeAdicValuationIdeal E (m - 1) ∧
      aeval x f + aeval x f.derivative * δ = 0 := by
  let := spectralNorm.nontriviallyNormedField ℚ_[3] E
  let d := aeval (x : E) f.derivative
  have hdpos : 0 < ‖d‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3⁻¹) hd
  have hd0 : d ≠ 0 := norm_pos_iff.mp hdpos
  have he (p : ℤ_[3][X]) : aeval (x : E) p =
      ((aeval x p : ThreeAdicIntegers E) : E) :=
    aeval_algHom_apply (ThreeAdicIntegers E).val x p
  have hx' : ‖aeval (x : E) f‖ ≤ (3 : ℝ) ^ (-(m : ℝ)) := by
    rw [he]
    exact hx
  let c : E := -aeval (x : E) f / d
  have hscale : (3 : ℝ) ^ (-(m : ℝ)) / (3 : ℝ)⁻¹ =
      (3 : ℝ) ^ (-((m - 1 : ℚ) : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_sub (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  have hc : ‖c‖ ≤ (3 : ℝ) ^ (-((m - 1 : ℚ) : ℝ)) := by
    calc
      ‖c‖ = ‖aeval (x : E) f‖ / ‖d‖ := by simp only [c, norm_div, norm_neg]
      _ ≤ (3 : ℝ) ^ (-(m : ℝ)) / ‖d‖ := div_le_div_of_nonneg_right hx' hdpos.le
      _ ≤ (3 : ℝ) ^ (-(m : ℝ)) / (3 : ℝ)⁻¹ :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hd
      _ = _ := hscale
  have hc1 : ‖c‖ ≤ 1 := hc.trans (Real.rpow_le_one_of_one_le_of_nonpos
    (by norm_num) (by exact_mod_cast (show -(m - 1) ≤ 0 by linarith)))
  let δ : ThreeAdicIntegers E :=
    ⟨c, (isIntegral_iff_spectralNorm_le_one E c).mpr hc1⟩
  refine ⟨δ, hc, ?_⟩
  apply Subtype.ext
  change (aeval x f : E) + (aeval x f.derivative : E) * c = 0
  rw [← he f, ← he f.derivative]
  change aeval (x : E) f + d * (-aeval (x : E) f / d) = 0
  field_simp
  ring

/-- Valuation cutoffs add under multiplication of integral elements. -/
theorem mul_mem_threeAdicValuationIdeal {m n : ℚ} {x y : ThreeAdicIntegers E}
    (hx : x ∈ threeAdicValuationIdeal E m) (hy : y ∈ threeAdicValuationIdeal E n) :
    x * y ∈ threeAdicValuationIdeal E (m + n) := by
  let := spectralNorm.nontriviallyNormedField ℚ_[3] E
  change ‖(x : E) * (y : E)‖ ≤ (3 : ℝ) ^ (-((m + n : ℚ) : ℝ))
  change ‖(x : E)‖ ≤ (3 : ℝ) ^ (-(m : ℝ)) at hx
  change ‖(y : E)‖ ≤ (3 : ℝ) ^ (-(n : ℝ)) at hy
  rw [norm_mul]
  calc
    _ ≤ (3 : ℝ) ^ (-(m : ℝ)) * (3 : ℝ) ^ (-(n : ℝ)) :=
      mul_le_mul hx hy (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      push_cast
      ring

/-- Cancelling the linear term leaves a quadratic error in a Newton step. -/
theorem newton_step_mem_valuationIdeal (f : ℤ_[3][X]) (x δ : ThreeAdicIntegers E)
    {t : ℚ} (hδ : δ ∈ threeAdicValuationIdeal E t)
    (hlin : aeval x f + aeval x f.derivative * δ = 0) :
    aeval (x + δ) f ∈ threeAdicValuationIdeal E (t + t) := by
  obtain ⟨q, hq⟩ := (f.map (algebraMap ℤ_[3] (ThreeAdicIntegers E))).binomExpansion x δ
  simp only [eval_map_algebraMap, derivative_map] at hq
  rw [hlin, zero_add] at hq
  rw [hq, pow_two]
  exact Ideal.mul_mem_left _ q (mul_mem_threeAdicValuationIdeal E hδ hδ)

/-- The monogenic Newton step doubles the precision remaining after a loss
of one. It improves precision whenever `m > 2`; no root existence is assumed. -/
theorem _root_.PowerBasis.exists_newton_step_of_three_smul
    {A : Type*} [CommRing A] [Algebra ℤ_[3] A] (pb : PowerBasis ℤ_[3] A)
    (hΩ : ∀ ω : KaehlerDifferential ℤ_[3] A, (3 : ℤ_[3]) • ω = 0)
    (x : ThreeAdicIntegers E) {m : ℚ} (hm : 1 < m)
    (hx : aeval x (minpoly ℤ_[3] pb.gen) ∈ threeAdicValuationIdeal E m) :
    ∃ y : ThreeAdicIntegers E,
      y - x ∈ threeAdicValuationIdeal E (m - 1) ∧
      aeval y (minpoly ℤ_[3] pb.gen) ∈ threeAdicValuationIdeal E (2 * (m - 1)) := by
  obtain ⟨δ, hδ, hlin⟩ := exists_integral_newton_correction E _ x hm hx
    (pb.spectralNorm_derivative_ge_of_three_smul E hΩ x hm hx)
  refine ⟨x + δ, by simpa only [add_sub_cancel_left] using hδ, ?_⟩
  simpa only [two_mul] using newton_step_mem_valuationIdeal E _ x δ hδ hlin

end ThreeAdicPlan
