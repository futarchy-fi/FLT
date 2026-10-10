/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalObstruction

/-!
# A vertical tangent obstruction at every affine Weierstrass singularity

Translation to a singular point removes the constant and linear terms. The
coefficient of the squared vertical direction is still one, in every
characteristic, so the vertical tangent cannot lift to third-order jets.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open Polynomial PolygonNodePresentation

variable {S : Type*} [CommRing S]

/-- Translating an affine singularity leaves only the quadratic and cubic terms. -/
theorem singularAffine_translate (W : WeierstrassCurve S) (x y u v : S)
    (he : y ^ 2 + W.a₁ * x * y + W.a₃ * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0)
    (hx : W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 0)
    (hy : 2 * y + W.a₁ * x + W.a₃ = 0) :
    (y + v) ^ 2 + W.a₁ * (x + u) * (y + v) + W.a₃ * (y + v) -
        ((x + u) ^ 3 + W.a₂ * (x + u) ^ 2 + W.a₄ * (x + u) + W.a₆) =
      v ^ 2 + W.a₁ * u * v - u ^ 3 - (3 * x + W.a₂) * u ^ 2 := by
  linear_combination he + u * hx + v * hy

variable {K : Type*} [Field K]

/-- Neither the mixed quadratic term nor the horizontal quadratic term removes the obstruction. -/
theorem singularAffineJet_obstruction (c d : K) (x y : Jet K 3)
    (hx : jetDrop x = 0) (hy : jetDrop y = jet 2 X) :
    y ^ 2 + algebraMap K _ c * x * y - x ^ 3 - algebraMap K _ d * x ^ 2 ≠ 0 := by
  obtain ⟨p, rfl⟩ := jet_surjective 3 x
  obtain ⟨q, rfl⟩ := jet_surjective 3 y
  have hp := (jet_eq_iff 2 p 0).mp (by simpa only [jetDrop_jet, map_zero] using hx)
  have hq := (jet_eq_iff 2 q X).mp hy
  have hp0 : p.coeff 0 = 0 := by simpa using hp 0 (by omega)
  have hp1 : p.coeff 1 = 0 := by simpa using hp 1 (by omega)
  have hq0 : q.coeff 0 = 0 := by simpa using hq 0 (by omega)
  have hq1 : q.coeff 1 = 1 := by simpa using hq 1 (by omega)
  intro h
  have hc := (jet_eq_iff 3 (q ^ 2 + C c * p * q - p ^ 3 - C d * p ^ 2) 0).mp (by
    have hC (z : K) : jet 3 (C z) = algebraMap K _ z := (jet 3).commutes z
    simpa only [map_sub, map_add, map_pow, map_mul, hC, map_zero] using h)
  have := hc 2 (by omega)
  simp [pow_succ, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, hp0, hp1, hq0, hq1] at this

end FLT.Mazur.WeierstrassIntegralChart
