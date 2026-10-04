/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.PadicCyclotomicRootTrace
public import Mathlib.Analysis.Normed.Ring.Ultra

/-! # Trace bounds on integral polynomials in cyclotomic roots -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
open Polynomial
variable (p : ℕ) [hp : Fact p.Prime]

/-- A p-power root has norm at most one. -/
theorem padicCyclotomic_root_norm_le_one (m : ℕ) (ζ : PadicAlgCl p)
    (hζ : ζ ^ (p ^ m) = 1) : ‖ζ‖ ≤ 1 := by
  apply le_of_pow_le_pow_left₀ (pow_ne_zero _ hp.out.ne_zero) (by positivity)
  rw [← norm_pow, hζ, norm_one, one_pow]

/-- The actual projection of any p-power root has norm at most one. -/
theorem padicCyclotomicProjection_root_norm_le_one (n m : ℕ) (ζ : PadicAlgCl p)
    (hζ : ζ ^ (p ^ m) = 1) : ‖padicCyclotomicProjection p (n + 1) ζ‖ ≤ 1 := by
  rw [padicCyclotomicProjection_root p n m ζ hζ]
  split_ifs
  · exact padicCyclotomic_root_norm_le_one p m ζ hζ
  · simp

/-- Integral polynomials in a root have projected norm at most one, uniformly in the level. -/
theorem padicCyclotomicProjection_intPolynomial_norm_le_one (n m : ℕ) (ζ : PadicAlgCl p)
    (hζ : ζ ^ (p ^ m) = 1) (f : ℤ[X]) :
    ‖padicCyclotomicProjection p (n + 1) (aeval ζ f)‖ ≤ 1 := by
  classical
  rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def, map_sum]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro i _
  have hr : (ζ ^ i) ^ (p ^ m) = 1 := by
    rw [← pow_mul, Nat.mul_comm i, pow_mul, hζ, one_pow]
  have hlin : padicCyclotomicProjection p (n + 1) ((f.coeff i : PadicAlgCl p) * ζ ^ i) =
      (f.coeff i : PadicAlgCl p) * padicCyclotomicProjection p (n + 1) (ζ ^ i) := by
    simpa only [zsmul_eq_mul] using map_zsmul (padicCyclotomicProjection p (n + 1))
      (f.coeff i) (ζ ^ i)
  change ‖padicCyclotomicProjection p (n + 1) ((f.coeff i : PadicAlgCl p) * ζ ^ i)‖ ≤ 1
  rw [hlin, norm_mul]
  exact (mul_le_mul (IsUltrametricDist.norm_intCast_le_one _ _)
    (padicCyclotomicProjection_root_norm_le_one p n m (ζ ^ i) hr)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- All powers of a cyclotomic uniformizer have projected norm at most one. -/
theorem padicCyclotomicProjection_uniformizer_pow_norm_le_one (n m i : ℕ)
    (ζ : PadicAlgCl p) (hζ : ζ ^ (p ^ m) = 1) :
    ‖padicCyclotomicProjection p (n + 1) ((ζ - 1) ^ i)‖ ≤ 1 := by
  have he : aeval ζ ((X - 1 : ℤ[X]) ^ i) = (ζ - 1) ^ i := by
    simp only [map_pow, map_sub, aeval_X, map_one]
  rw [← he]
  exact padicCyclotomicProjection_intPolynomial_norm_le_one p n m ζ hζ ((X - 1) ^ i)

end PadicHodgeTheory
