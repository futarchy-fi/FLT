/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalIntegerMultiplication
public import FLT.Mazur.EllipticLocalMultiplication

/-!
# Convergent integer multiplication on actual E₁ points

The integral formal inverse evaluates to actual negation. Consequently the
integer multiplication series computes every integer multiple of an E₁ point.
-/

@[expose] public section

namespace FLT.Mazur
open IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
variable [IsAdicComplete (maximalIdeal A) A]

/-- Convergent formal inversion gives actual negation in the reduction kernel. -/
theorem localE1Point_evaluation_negate {σ : Type*} [Finite σ] (a : σ → A)
    (ha : ∀ i, a i ∈ maximalIdeal A) {t : MvPowerSeries σ A}
    (ht : t.constantCoeff = 0) :
    localE1Point A W (localMvEvaluation A a ha (FormalInfinity.negate W t))
      (localMvEvaluation_mem A a ha (FormalInfinity.constantCoeff_negate W ht)) =
      -localE1Point A W (localMvEvaluation A a ha t) (localMvEvaluation_mem A a ha ht) := by
  have h := localE1Point_evaluation_add A W a ha ht (FormalInfinity.constantCoeff_negate W ht)
  have hz : localE1Point A W (localMvEvaluation A a ha
      (FormalInfinity.add W t (FormalInfinity.negate W t)))
      (localMvEvaluation_mem A a ha (FormalInfinity.constantCoeff_add W ht
        (FormalInfinity.constantCoeff_negate W ht))) = 0 := by
    simp only [FormalInfinity.add_negate W ht, map_zero, localE1Point_zero]
  rw [hz] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- Convergent integer multiplication gives actual integer scalar multiplication. -/
theorem localE1Point_evaluation_integerMultiply {σ : Type*} [Finite σ] (a : σ → A)
    (ha : ∀ i, a i ∈ maximalIdeal A) (n : ℤ) {t : MvPowerSeries σ A}
    (ht : t.constantCoeff = 0) :
    localE1Point A W (localMvEvaluation A a ha (FormalInfinity.integerMultiply W n t))
      (localMvEvaluation_mem A a ha (FormalInfinity.constantCoeff_integerMultiply W n ht)) =
      n • localE1Point A W (localMvEvaluation A a ha t) (localMvEvaluation_mem A a ha ht) := by
  cases n with
  | ofNat n =>
    simpa only [FormalInfinity.integerMultiply, Int.ofNat_eq_natCast, natCast_zsmul] using
      localE1Point_evaluation_multiply A W a ha n ht
  | negSucc n =>
    simp only [FormalInfinity.integerMultiply,
      localE1Point_evaluation_negate A W a ha (FormalInfinity.constantCoeff_multiply W (n + 1) ht),
      localE1Point_evaluation_multiply A W a ha (n + 1) ht, negSucc_zsmul]

/-- The actual E₁ integer-multiple parameter is the evaluated integral series. -/
theorem infinityParameter_zsmul (n : ℤ) (P : ellipticE1 A W) :
    infinityParameter A W (n • P) =
      localSeriesEvaluation A (infinityParameter A W P) (infinityParameter_mem A W P)
        (FormalInfinity.integerMultiplicationSeries W n) := by
  have h := localE1Point_evaluation_integerMultiply A W (fun _ : Unit => infinityParameter A W P)
    (fun _ => infinityParameter_mem A W P) n (t := PowerSeries.X) (by simp [PowerSeries.X])
  have hp := congrArg (infinityParameter A W) h
  simpa only [infinityParameter_localE1Point, localMvEvaluation_unit,
    localSeriesEvaluation_X, localE1Point_infinityParameter,
    FormalInfinity.integerMultiplicationSeries] using hp.symm

end FLT.Mazur
