/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.PrimeSummability
public import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# The logarithmic Euler product for Dedekind zeta

This proves part (i) of leaf Z3 in `docs/CHEBOTAREV_PLAN.md`. As in Z2, the
plan's `Prime K` and `norm v` are spelled out as `HeightOneSpectrum (𝓞 K)` and
`v.asIdeal.absNorm`. The logarithm is the real logarithm of the real part of zeta.
-/

public section

open NumberField IsDedekindDomain

namespace Chebotarev

/-- The logarithmic prime-ideal Euler series converges for real `s > 1`. -/
theorem summable_neg_log_one_sub_primeNorm (K : Type*) [Field K] [NumberField K]
    (s : ℝ) (hs : 1 < s) :
    Summable (fun v : HeightOneSpectrum (𝓞 K) ↦
      -Real.log (1 - (v.asIdeal.absNorm : ℝ) ^ (-s))) := by
  simpa only [sub_eq_add_neg] using
    (Real.summable_log_one_add_of_summable (summable_primeNorm K s hs).neg).neg

/-- For real `s > 1`, the logarithm of Dedekind zeta is the convergent sum of
negative logarithms of the prime-ideal Euler denominators. -/
theorem log_dedekindZeta_eq_tsum_primeIdeal (K : Type*) [Field K] [NumberField K]
    (s : ℝ) (hs : 1 < s) :
    Real.log (NumberField.dedekindZeta K (s : ℂ)).re =
      ∑' v : HeightOneSpectrum (𝓞 K),
        -Real.log (1 - (v.asIdeal.absNorm : ℝ) ^ (-s)) := by
  let e : HeightOneSpectrum (𝓞 K) ≃
      {p : Ideal (𝓞 K) // p.IsPrime ∧ p ≠ ⊥} :=
    { toFun := fun v ↦ ⟨v.asIdeal, v.isPrime, v.ne_bot⟩
      invFun := fun p ↦ ⟨p.1, p.2.1, p.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hcast (v : HeightOneSpectrum (𝓞 K)) :
      (((v.asIdeal.absNorm : ℝ) ^ (-s) : ℝ) : ℂ) =
        (v.asIdeal.absNorm : ℂ) ^ (-(s : ℂ)) := by
    simp only [Complex.ofReal_cpow (Nat.cast_nonneg _) (-s),
      Complex.ofReal_natCast, Complex.ofReal_neg]
  have hpos (v : HeightOneSpectrum (𝓞 K)) :
      0 < 1 - (v.asIdeal.absNorm : ℝ) ^ (-s) := by
    have h := norm_absNorm_cpow_neg_lt_one K (s := (s : ℂ)) hs (e v)
    change ‖(v.asIdeal.absNorm : ℂ) ^ (-(s : ℂ))‖ < 1 at h
    rw [← hcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at h
    exact sub_pos.mpr h
  have hsum := summable_neg_log_one_sub_primeNorm K s hs
  have hprod := Real.hasProd_of_hasSum_log
    (fun v ↦ inv_pos.mpr (hpos v))
    (show HasSum (fun v : HeightOneSpectrum (𝓞 K) ↦
        Real.log ((1 - (v.asIdeal.absNorm : ℝ) ^ (-s))⁻¹))
      (∑' v : HeightOneSpectrum (𝓞 K),
        -Real.log (1 - (v.asIdeal.absNorm : ℝ) ^ (-s))) by
      simpa only [Real.log_inv] using hsum.hasSum)
  have hprodC := hprod.map Complex.ofRealHom.toMonoidHom Complex.continuous_ofReal
  have hzeta : NumberField.dedekindZeta K (s : ℂ) =
      (Real.exp (∑' v : HeightOneSpectrum (𝓞 K),
        -Real.log (1 - (v.asIdeal.absNorm : ℝ) ^ (-s))) : ℂ) := by
    rw [dedekindZeta_eq_tprod_primeIdeal K hs, ← e.tprod_eq]
    calc
      _ = ∏' v : HeightOneSpectrum (𝓞 K),
          (((1 - (v.asIdeal.absNorm : ℝ) ^ (-s))⁻¹ : ℝ) : ℂ) := by
        apply tprod_congr
        intro v
        change (1 - (v.asIdeal.absNorm : ℂ) ^ (-(s : ℂ)))⁻¹ = _
        rw [Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one, hcast]
      _ = _ := hprodC.tprod_eq
  rw [hzeta, Complex.ofReal_re, Real.log_exp]

end Chebotarev
