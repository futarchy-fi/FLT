/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.KnownIn1980s.EllipticCurves.TateCurve
public import FLT.TateCurve.Integral
public import FLT.TateCurve.LocalField

/-!
# Evaluation of the formal Tate coordinate equation

Unconditional convergence over a complete nonarchimedean field allows evaluation
of Cauchy products. The specialized integral identity then gives the curve equation
whenever the coordinate expansions have their claimed sums.
-/

@[expose] public section

open scoped PowerSeries
open ValuativeRel

namespace TateCurve

section Evaluation

variable {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
  [NonarchimedeanRing K] [T3Space K]

/-- Evaluation of a product of convergent power series is the product of their sums
in a complete nonarchimedean field. -/
theorem hasSum_coeff_mul {q a b : K} {F G : K⟦X⟧}
    (hF : HasSum (fun n ↦ PowerSeries.coeff n F * q ^ n) a)
    (hG : HasSum (fun n ↦ PowerSeries.coeff n G * q ^ n) b) :
    HasSum (fun n ↦ PowerSeries.coeff n (F * G) * q ^ n) (a * b) := by
  have hp := hF.summable.mul_of_nonarchimedean hG.summable
  have hs := (summable_sum_mul_range_of_summable_mul
    (f := fun n : ℕ ↦ PowerSeries.coeff n F * q ^ n)
    (g := fun n : ℕ ↦ PowerSeries.coeff n G * q ^ n) hp).hasSum
  rw [← hF.summable.tsum_mul_tsum_eq_tsum_sum_range hG.summable hp,
    hF.tsum_eq, hG.tsum_eq] at hs
  refine hs.congr_fun fun n ↦ ?_
  rw [PowerSeries.coeff_mul, Finset.sum_mul,
    ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j ↦ (PowerSeries.coeff i F * q ^ i) * (PowerSeries.coeff j G * q ^ j))]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.mem_antidiagonal.mp hp, pow_add]
  ring

/-- Evaluation of a nonnegative power of a convergent series commutes with powers. -/
theorem hasSum_coeff_pow {q a : K} {F : K⟦X⟧}
    (hF : HasSum (fun n ↦ PowerSeries.coeff n F * q ^ n) a) (m : ℕ) :
    HasSum (fun n ↦ PowerSeries.coeff n (F ^ m) * q ^ n) (a ^ m) := by
  induction m with
  | zero =>
    simp only [pow_zero]
    convert (hasSum_ite_eq (0 : ℕ) (1 : K)) using 1
    funext n
    by_cases hn : n = 0 <;> simp [PowerSeries.coeff_one, hn]
  | succ m hm => simpa only [pow_succ] using hasSum_coeff_mul hm hF

end Evaluation

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Sums of the specialized formal Tate coordinates satisfy the affine Tate equation.
This isolates the remaining analytic input: the two coordinate expansion formulas. -/
theorem equation_of_hasSum_coordinates {q u x y : K} (hq : valuation K q < 1)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1)
    (hx : HasSum (fun n ↦ PowerSeries.coeff n (integralX u u⁻¹ (1 - u)⁻¹) * q ^ n) x)
    (hy : HasSum (fun n ↦ PowerSeries.coeff n (integralY u u⁻¹ (1 - u)⁻¹) * q ^ n) y) :
    (WeierstrassCurve.tateCurve q).toAffine.Equation x y := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  have h4 : HasSum (fun n ↦ PowerSeries.coeff n
      (PowerSeries.map (Int.castRingHom K) a₄Formal) * q ^ n) (evalInt q a₄Formal) :=
    (summable_evalInt q hq a₄Formal).hasSum
  have h6 : HasSum (fun n ↦ PowerSeries.coeff n
      (PowerSeries.map (Int.castRingHom K) a₆Formal) * q ^ n) (evalInt q a₆Formal) :=
    (summable_evalInt q hq a₆Formal).hasSum
  have hl := (hasSum_coeff_pow hy 2).add (hasSum_coeff_mul hx hy)
  have hr := ((hasSum_coeff_pow hx 3).add (hasSum_coeff_mul h4 hx)).add h6
  have heq : y ^ 2 + x * y = x ^ 3 + evalInt q a₄Formal * x + evalInt q a₆Formal := by
    apply HasSum.unique hl
    convert hr using 1
    funext n
    have h := congrArg (fun F : K⟦X⟧ ↦ PowerSeries.coeff n F * q ^ n)
      (specialized_weierstrass_equation u hu0 hu1)
    simpa only [map_add, add_mul] using h
  simpa [WeierstrassCurve.Affine.equation_iff, WeierstrassCurve.tateCurve,
    WeierstrassCurve.tateA₄_eq_evalInt q hq, WeierstrassCurve.tateA₆_eq_evalInt q hq] using heq

end TateCurve
