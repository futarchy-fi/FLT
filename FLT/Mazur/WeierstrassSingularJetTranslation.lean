/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSingularJetObstruction

/-!
# Jets at arbitrary affine singular points

The constant coordinates are retained, so the obstruction applies directly to
the original equation without transporting the curve to a normal form.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open Polynomial PolygonNodePresentation WeierstrassCurve

variable {K : Type*} [Field K] (W : WeierstrassCurve K) (x y : K)

/-- At a vertical critical point, the vertical infinitesimal vector satisfies the equation. -/
theorem singularAffineJet_tangent_equation (he : W.toAffine.Equation x y)
    (hy : 2 * y + W.a₁ * x + W.a₃ = 0) :
    (W.map (algebraMap K (Jet K 2))).toAffine.Equation
      (algebraMap K _ x) (algebraMap K _ y + jet 2 X) := by
  rw [Affine.equation_iff'] at he ⊢
  have h : jet 2 ((C y + X) ^ 2 + C W.a₁ * C x * (C y + X) +
      C W.a₃ * (C y + X) -
        ((C x) ^ 3 + C W.a₂ * (C x) ^ 2 + C W.a₄ * C x + C W.a₆)) = 0 := by
    rw [← map_zero (jet 2), jet_eq_iff]
    intro d hd
    interval_cases d <;>
      simp [pow_succ, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ]
    · linear_combination he
    · linear_combination hy
  have hC (z : K) : jet 2 (C z) = algebraMap K _ z := (jet 2).commutes z
  simpa only [map_sub, map_add, map_mul, map_pow, hC, WeierstrassCurve.map, toAffine] using h

/-- No third-order lift of the vertical tangent satisfies the equation at a singular point. -/
theorem singularAffineJet_no_lift
    (hx : W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 0)
    (hy : 2 * y + W.a₁ * x + W.a₃ = 0)
    (u v : Jet K 3) (hu : jetDrop u = algebraMap K _ x)
    (hv : jetDrop v = algebraMap K _ y + jet 2 X) :
    ¬ (W.map (algebraMap K (Jet K 3))).toAffine.Equation u v := by
  obtain ⟨p, rfl⟩ := jet_surjective 3 u
  obtain ⟨q, rfl⟩ := jet_surjective 3 v
  have hC2 (z : K) : jet 2 (C z) = algebraMap K _ z := (jet 2).commutes z
  have hp := (jet_eq_iff 2 p (C x)).mp (by simpa only [jetDrop_jet, hC2] using hu)
  have hq := (jet_eq_iff 2 q (C y + X)).mp
    (by simpa only [jetDrop_jet, map_add, hC2] using hv)
  have hp0 : p.coeff 0 = x := by simpa using hp 0 (by omega)
  have hp1 : p.coeff 1 = 0 := by simpa using hp 1 (by omega)
  have hq0 : q.coeff 0 = y := by simpa using hq 0 (by omega)
  have hq1 : q.coeff 1 = 1 := by simpa using hq 1 (by omega)
  intro he
  rw [Affine.equation_iff'] at he
  have hc := (jet_eq_iff 3
      (q ^ 2 + C W.a₁ * p * q + C W.a₃ * q -
        (p ^ 3 + C W.a₂ * p ^ 2 + C W.a₄ * p + C W.a₆)) 0).mp (by
    have hC (z : K) : jet 3 (C z) = algebraMap K _ z := (jet 3).commutes z
    simpa only [map_sub, map_add, map_pow, map_mul, hC, map_zero,
      WeierstrassCurve.map, toAffine] using he)
  have hc2 := hc 2 (by omega)
  simp only [pow_succ, pow_zero, one_mul, coeff_sub, coeff_add, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.succ_eq_add_one, Nat.reduceAdd,
    Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, hq0, tsub_zero, hq1,
    Nat.add_one_sub_one, mul_one, tsub_self, hp0, Finset.range_zero, zero_tsub,
    Finset.sum_empty, coeff_C_zero, zero_add, hp1, mul_zero, coeff_C_succ, zero_mul,
    add_zero, coeff_zero] at hc2
  have hh : (1 : K) = 0 := by
    linear_combination hc2 - p.coeff 2 * hx - q.coeff 2 * hy
  exact one_ne_zero hh

end FLT.Mazur.WeierstrassIntegralChart
