/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXTotalTransform

/-!
# The original fractions satisfy the x-direction equation

Inside an algebra where the original horizontal coordinate is invertible,
evaluate the proved total-transform identity at s/x, y/x, x. Cancellation of
the horizontal square gives the actual divided equation.
-/

@[expose] public noncomputable section

open MvPolynomial WeierstrassCurve

namespace FLT.Mazur.WeierstrassModificationX

set_option backward.isDefEq.respectTransparency false

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (f : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] S)
  (d : S) (hd : f (WeierstrassIntegralChart.coord W 2 0) * d = 1)

include h3 h4 h6 hd

/-- The actual original fractions recover the original horizontal coordinate. -/
theorem fraction_horizontal :
    f (WeierstrassIntegralChart.coord W 2 0) =
      (d * f (WeierstrassIntegralChart.coord W 2 1)) ^ 2 +
        (algebraMap R S W.a₁ + algebraMap R S b3 * (d * algebraMap R S s)) *
          (d * f (WeierstrassIntegralChart.coord W 2 1)) -
        (algebraMap R S W.a₂ + algebraMap R S b4 * (d * algebraMap R S s) +
          algebraMap R S b6 * (d * algebraMap R S s) ^ 2) := by
  let c : Fin 3 → S := ![d * algebraMap R S s,
    d * f (WeierstrassIntegralChart.coord W 2 1),
    f (WeierstrassIntegralChart.coord W 2 0)]
  have hc0 : c 0 = d * algebraMap R S s := rfl
  have hc1 : c 1 = d * f (WeierstrassIntegralChart.coord W 2 1) := rfl
  have hc2 : c 2 = f (WeierstrassIntegralChart.coord W 2 0) := rfl
  have hi : aeval c (incidencePolynomial s) = 0 := by
    simp only [incidencePolynomial, map_sub, map_mul, aeval_X, aeval_C, hc0, hc2]
    linear_combination algebraMap R S s * hd
  have ho : aeval c (originalTransformPolynomial W) = 0 := by
    have he := WeierstrassIntegralChart.coord_equation W 2
    rw [Projective.equation_iff] at he
    have hm := congrArg f he
    simp only [map_sub, map_add, map_mul, map_pow, map_zero, AlgHom.commutes,
      map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, WeierstrassIntegralChart.coord_self,
      mul_one, one_pow] at hm
    have hxy : f (WeierstrassIntegralChart.coord W 2 0) *
        (d * f (WeierstrassIntegralChart.coord W 2 1)) =
          f (WeierstrassIntegralChart.coord W 2 1) := by rw [← mul_assoc, hd, one_mul]
    simpa only [originalTransformPolynomial, map_sub, map_add, map_mul, map_pow,
      aeval_X, aeval_C, hc1, hc2, hxy] using hm
  have he := congrArg (aeval c) (originalTransform_identity W s b3 b4 b6 h3 h4 h6)
  simp only [map_add, map_mul, map_pow, aeval_X, hi, ho, zero_add, zero_mul] at he
  have hu := (isUnit_iff_exists_inv.mpr ⟨d, hd⟩).isRegular
  have hz : aeval c (strictPolynomial W b3 b4 b6) = 0 :=
    (hu.pow 2).left (he.trans (mul_zero _).symm)
  simpa only [strictPolynomial, horizontalPolynomial, map_sub, map_add, map_mul,
    map_pow, aeval_X, aeval_C, hc0, hc1, hc2, sub_eq_zero] using hz

/-- The original fraction coordinates satisfy the actual x-chart incidence equation. -/
theorem fraction_incidence :
    (d * algebraMap R S s) *
      ((d * f (WeierstrassIntegralChart.coord W 2 1)) ^ 2 +
        (algebraMap R S W.a₁ + algebraMap R S b3 * (d * algebraMap R S s)) *
          (d * f (WeierstrassIntegralChart.coord W 2 1)) -
        (algebraMap R S W.a₂ + algebraMap R S b4 * (d * algebraMap R S s) +
          algebraMap R S b6 * (d * algebraMap R S s) ^ 2)) = algebraMap R S s := by
  rw [← fraction_horizontal W s b3 b4 b6 h3 h4 h6 f d hd]
  linear_combination algebraMap R S s * hd

end FLT.Mazur.WeierstrassModificationX
