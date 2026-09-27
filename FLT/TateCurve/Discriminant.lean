/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.TateCurve.Elliptic

import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction

/-!
# The formal Tate discriminant

The discriminant of the integral Tate equation equals
`X * (∏' n, (1 - X ^ (n + 1))) ^ 24`.
We compare their complex q-expansions, using the pentagonal number theorem
for the product and the modular identity `1728 Δ = E₄³ - E₆²` for the equation.
Injectivity of the integer embedding then gives the integral formal identity.
-/

@[expose] public section

open scoped PowerSeries PowerSeries.WithPiTopology ArithmeticFunction.sigma
open PowerSeries ModularForm EisensteinSeries UpperHalfPlane
namespace TateCurve

/-- Complex convergent multiplication for power series. -/
private theorem hasSum_complex_mul {q a b : ℂ} {F G : ℂ⟦X⟧}
    (hF : HasSum (fun n ↦ coeff n F * q ^ n) a)
    (hG : HasSum (fun n ↦ coeff n G * q ^ n) b) :
    HasSum (fun n ↦ coeff n (F * G) * q ^ n) (a * b) := by
  have h := hasSum_sum_range_mul_of_summable_norm hF.summable.norm hG.summable.norm
  rw [hF.tsum_eq, hG.tsum_eq] at h
  refine h.congr_fun fun n ↦ ?_
  rw [coeff_mul, ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j ↦ (coeff i F * q ^ i) * (coeff j G * q ^ j)), Finset.sum_mul]
  exact Finset.sum_congr rfl fun p hp ↦ by rw [← Finset.mem_antidiagonal.mp hp, pow_add]; ring

/-- Complex convergent powers of a power series. -/
private theorem hasSum_complex_pow {q a : ℂ} {F : ℂ⟦X⟧}
    (hF : HasSum (fun n ↦ coeff n F * q ^ n) a) (m : ℕ) :
    HasSum (fun n ↦ coeff n (F ^ m) * q ^ n) (a ^ m) := by
  induction m with
  | zero =>
    simp only [pow_zero]
    convert (hasSum_ite_eq (0 : ℕ) (1 : ℂ)) using 1
    ext n
    by_cases hn : n = 0 <;> simp [hn]
  | succ m hm => simpa only [pow_succ] using hasSum_complex_mul hm hF

/-- The formal product discriminant has the modular discriminant's q-expansion. -/
private theorem map_ΔFormal : PowerSeries.map (Int.castRingHom ℂ) ΔFormal =
    qExpansion 1 ModularForm.discriminant := by
  ext n
  apply (ModularFormClass.qExpansion_coeff_unique zero_lt_one one_mem_strictPeriods_SL
    (f := CuspForm.discriminant) ?_ n)
  intro τ
  let q : ℂ := Function.Periodic.qParam 1 τ
  have hq : ‖q‖ < 1 := by simpa [q] using UpperHalfPlane.norm_qParam_lt_one 1 τ
  have hEuler := hasSum_eulerFunction_pentagonalSeries (R := ℂ) hq
  rw [eulerFunction_eq_tprod hq] at hEuler
  have hprod : PowerSeries.map (Int.castRingHom ℂ)
      (∏' n : ℕ, (1 - (X : ℤ⟦X⟧) ^ (n + 1))) = pentagonalSeries ℂ := by
    rw [PowerSeries.WithPiTopology.tprod_one_sub_X_pow]
    ext i
    by_cases hi : i ∈ Set.range pentagonal
    · obtain ⟨k, rfl⟩ := hi
      simp
    · simp [coeff_pentagonalSeries_eq_zero ℤ hi, coeff_pentagonalSeries_eq_zero ℂ hi]
  have hX : HasSum (fun n ↦ coeff n (X : ℂ⟦X⟧) * q ^ n) q := by
    convert (hasSum_ite_eq (1 : ℕ) q) using 1
    funext n
    by_cases hn : n = 1 <;> simp [coeff_X, hn]
  have hs : Summable (fun n : ℕ ↦ ‖q ^ (n + 1)‖) := by
    simpa only [norm_pow] using
      (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg q) hq)
  have hm : Multipliable (fun n : ℕ ↦ (1 - q ^ (n + 1))) :=
    multipliable_one_sub_of_summable hs
  have h := hasSum_complex_mul hX (hasSum_complex_pow hEuler 24)
  simp only [ΔFormal, map_mul, map_pow, PowerSeries.map_X, hprod, smul_eq_mul]
  convert h using 1
  change ModularForm.discriminant τ = q * (∏' n : ℕ, (1 - q ^ (n + 1))) ^ 24
  rw [ModularForm.discriminant_eq_q_prod]
  exact congrArg (q * ·) (hm.tprod_pow 24)


/-- The formal Tate c4 invariant is its Eisenstein series. -/
theorem formalCurve_c₄ : formalCurve.c₄ = c₄Formal := by
  simp only [formalCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, c₄Formal, a₄Formal]
  ring

/-- The coefficient divisibility that makes a6 integral. -/
theorem twelve_dvd_sigma (n : ℕ) : (12 : ℤ) ∣ 5 * (σ 3 n : ℤ) + 7 * (σ 5 n : ℤ) := by
  have hd : ∀ d : ℤ, (12 : ℤ) ∣ 5 * d ^ 3 + 7 * d ^ 5 := by
    intro d
    have h : ((5 * d ^ 3 + 7 * d ^ 5 : ℤ) : ZMod 12) = 0 := by
      push_cast
      generalize (d : ZMod 12) = r
      revert r
      decide
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12).mp h
  have heq : 5 * (σ 3 n : ℤ) + 7 * (σ 5 n : ℤ) =
      ∑ d ∈ n.divisors, (5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5) := by
    simp [ArithmeticFunction.sigma_apply, Finset.sum_add_distrib, Finset.mul_sum]
  rw [heq]
  exact Finset.dvd_sum fun d _ ↦ hd d

/-- The formal coefficient a6 satisfies its exact integral division identity. -/
theorem twelve_mul_a₆Formal : 12 * a₆Formal = -(5 * sInt 3 + 7 * sInt 5) := by
  ext n
  simp only [show (12 : ℤ⟦X⟧) = C 12 from by simp,
    coeff_C_mul, coeff_a₆Formal, map_neg, map_add,
    show (5 : ℤ⟦X⟧) = C 5 from by simp,
    show (7 : ℤ⟦X⟧) = C 7 from by simp, sInt, coeff_mk]
  rw [mul_neg, Int.mul_ediv_cancel' (twelve_dvd_sigma n)]

/-- The formal Tate c6 invariant is the negative of the weight-six Eisenstein series. -/
theorem formalCurve_c₆ : formalCurve.c₆ = -1 + 504 * sInt 5 := by
  have h := twelve_mul_a₆Formal
  simp only [formalCurve, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, a₄Formal]
  linear_combination -72 * h

/-- Complex coefficients identify c4 with E4's q-expansion. -/
private theorem map_c₄Formal : PowerSeries.map (Int.castRingHom ℂ) c₄Formal = qExpansion 1 E₄ := by
  ext n
  rw [coeff_map, E_qExpansion_coeff _ ⟨2, rfl⟩]
  norm_num [c₄Formal, sInt, PowerSeries.coeff_one, coeff_C_mul,
    show (240 : ℤ⟦X⟧) = C 240 from by simp,
    show bernoulli 4 = -1 / 30 by decide +kernel]
  split_ifs with hn
  · subst n; simp
  · simp

/-- Complex coefficients identify c6 with minus E6's q-expansion. -/
private theorem map_formalCurve_c₆ : PowerSeries.map (Int.castRingHom ℂ) formalCurve.c₆ =
    -qExpansion 1 E₆ := by
  rw [formalCurve_c₆]
  ext n
  rw [coeff_map, map_neg, E_qExpansion_coeff _ ⟨3, rfl⟩]
  norm_num [sInt, PowerSeries.coeff_one, coeff_C_mul,
    show (504 : ℤ⟦X⟧) = C 504 from by simp,
    show bernoulli 6 = 1 / 42 by decide +kernel]
  split_ifs with hn
  · subst n; simp
  · simp

/-- The formal Tate discriminant equals the product discriminant used in the j-series. -/
theorem formalCurve_Δ : formalCurve.Δ = ΔFormal := by
  apply PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective
  rw [map_ΔFormal]
  ext n
  apply ModularFormClass.qExpansion_coeff_unique zero_lt_one one_mem_strictPeriods_SL
    (f := CuspForm.discriminant) ?_ n
  intro τ
  have h4 := ModularForm.hasSum_qExpansion E₄ zero_lt_one one_mem_strictPeriods_SL τ
  have h6 := ModularForm.hasSum_qExpansion E₆ zero_lt_one one_mem_strictPeriods_SL τ
  have h := ((hasSum_complex_pow h4 3).sub (hasSum_complex_pow h6 2)).div_const 1728
  rw [← ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ] at h
  refine h.congr_fun fun m ↦ ?_
  have hc := congrArg (fun F : ℤ⟦X⟧ ↦ PowerSeries.map (Int.castRingHom ℂ) F)
    formalCurve.c_relation
  rw [map_mul, map_sub, map_pow, map_pow, formalCurve_c₄, map_c₄Formal,
    map_formalCurve_c₆, neg_sq] at hc
  have hm := congrArg (coeff m) hc
  have h1728 : PowerSeries.map (Int.castRingHom ℂ) (1728 : ℤ⟦X⟧) = C 1728 := by
    rw [show (1728 : ℤ⟦X⟧) = C 1728 from by simp, PowerSeries.map_C]
    rfl
  rw [h1728, coeff_C_mul] at hm
  simp only [map_sub] at hm
  simp only [smul_eq_mul]
  linear_combination hm * (Function.Periodic.qParam 1 τ ^ m) / 1728
end TateCurve
