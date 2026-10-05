/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticLocalAddition

/-!
# Actual E₁ multiplication and its convergent formal series

Natural scalar multiplication on the reduction kernel is computed by the
integral multiplication series. Its quadratic remainder gives a concrete local
expansion, and a unit scalar preserves the parameter up to an integral unit.
-/

@[expose] public section

namespace FLT.Mazur
open IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
variable [IsAdicComplete (maximalIdeal A) A]

/-- Zero is the identity in the convergent chart. -/
@[simp] theorem localE1Point_zero (h : (0 : A) ∈ maximalIdeal A) :
    localE1Point A W 0 h = 0 := by
  apply infinityParameter_injective A W
  simp

/-- Evaluating repeated formal sums gives actual natural scalar multiplication. -/
theorem localE1Point_evaluation_multiply {σ : Type*} [Finite σ] (a : σ → A)
    (ha : ∀ i, a i ∈ maximalIdeal A) (n : ℕ) {t : MvPowerSeries σ A}
    (ht : t.constantCoeff = 0) :
    localE1Point A W (localMvEvaluation A a ha (FormalInfinity.multiply W n t))
      (localMvEvaluation_mem A a ha (FormalInfinity.constantCoeff_multiply W n ht)) =
      n • localE1Point A W (localMvEvaluation A a ha t) (localMvEvaluation_mem A a ha ht) := by
  induction n with
  | zero => simp [FormalInfinity.multiply]
  | succ n ih =>
    simp only [FormalInfinity.multiply, localE1Point_evaluation_add A W a ha
      (FormalInfinity.constantCoeff_multiply W n ht) ht, ih, succ_nsmul]

/-- The one-variable specialization is the previously constructed convergent evaluation. -/
theorem localMvEvaluation_unit (t : A) (ht : t ∈ maximalIdeal A) :
    localMvEvaluation A (fun _ : Unit => t) (fun _ => ht) = localSeriesEvaluation A t ht := rfl

/-- The actual E₁ scalar multiple is computed by the integral multiplication series. -/
theorem infinityParameter_nsmul (n : ℕ) (P : ellipticE1 A W) :
    infinityParameter A W (n • P) =
      localSeriesEvaluation A (infinityParameter A W P) (infinityParameter_mem A W P)
        (FormalInfinity.multiplicationSeries W n) := by
  have h := localE1Point_evaluation_multiply A W (fun _ : Unit => infinityParameter A W P)
    (fun _ => infinityParameter_mem A W P) n (t := PowerSeries.X) (by simp [PowerSeries.X])
  have hp := congrArg (infinityParameter A W) h
  simpa only [infinityParameter_localE1Point, localMvEvaluation_unit,
    localSeriesEvaluation_X, localE1Point_infinityParameter,
    FormalInfinity.multiplicationSeries] using hp.symm

/-- The parameter of nP is nt plus an integral quadratic remainder. -/
theorem infinityParameter_nsmul_expansion (n : ℕ) (P : ellipticE1 A W) :
    ∃ r : A, infinityParameter A W (n • P) =
      n * infinityParameter A W P + infinityParameter A W P ^ 2 * r := by
  obtain ⟨g, hg⟩ := FormalInfinity.X_sq_dvd_multiplicationSeries_sub_linear W n
  have h := congrArg
    (localSeriesEvaluation A (infinityParameter A W P) (infinityParameter_mem A W P)) hg
  refine ⟨localSeriesEvaluation A (infinityParameter A W P) (infinityParameter_mem A W P) g, ?_⟩
  rw [infinityParameter_nsmul A W]
  simpa only [map_sub, map_mul, map_pow, localSeriesEvaluation_C,
    localSeriesEvaluation_X, sub_eq_iff_eq_add, add_comm] using h

/-- Multiplication by an integral unit preserves the E₁ parameter up to a unit. -/
theorem infinityParameter_nsmul_unit (n : ℕ) (hn : IsUnit (n : A)) (P : ellipticE1 A W) :
    ∃ u : Aˣ, infinityParameter A W (n • P) = infinityParameter A W P * u := by
  obtain ⟨r, hr⟩ := infinityParameter_nsmul_expansion A W n P
  have ht := (residue_eq_zero_iff _).mpr (infinityParameter_mem A W P)
  have hu : IsUnit ((n : A) + infinityParameter A W P * r) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    simpa only [map_add, map_mul, ht, zero_mul, add_zero] using (hn.map (residue A)).ne_zero
  refine ⟨hu.unit, ?_⟩
  rw [hu.unit_spec, hr]
  ring

/-- Unit-order torsion cannot occur in the actual reduction kernel. -/
theorem ellipticE1_nsmul_eq_zero_iff (n : ℕ) (hn : IsUnit (n : A)) (P : ellipticE1 A W) :
    n • P = 0 ↔ P = 0 := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := infinityParameter_nsmul_unit A W n hn P
    rw [h, infinityParameter_zero] at hu
    apply (infinityParameter_eq_zero_iff A W P).mp
    exact u.isUnit.mul_left_eq_zero.mp hu.symm
  · rintro rfl
    exact nsmul_zero n

end FLT.Mazur
