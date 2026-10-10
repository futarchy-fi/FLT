/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationYTotalTransform

/-!
# Original fractions satisfy the y-direction equation

Evaluate the original total transform at r=s/y, u=x/y, z=y and cancel y².
The incidence correction vanishes because the original vertical is inverted.
-/

@[expose] public noncomputable section

open MvPolynomial WeierstrassCurve

namespace FLT.Mazur.WeierstrassModificationY

set_option backward.isDefEq.respectTransparency false

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (f : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] S)
  (d : S) (hd : f (WeierstrassIntegralChart.coord W 2 1) * d = 1)

include h3 h4 h6 hd

/-- The three original fractions satisfy the divided y-chart cubic. -/
theorem fraction_equation :
    1 + algebraMap R S W.a₁ * (d * f (WeierstrassIntegralChart.coord W 2 0)) +
        algebraMap R S b3 * (d * algebraMap R S s) =
      f (WeierstrassIntegralChart.coord W 2 1) *
          (d * f (WeierstrassIntegralChart.coord W 2 0)) ^ 3 +
        algebraMap R S W.a₂ * (d * f (WeierstrassIntegralChart.coord W 2 0)) ^ 2 +
        algebraMap R S b4 * (d * algebraMap R S s) *
          (d * f (WeierstrassIntegralChart.coord W 2 0)) +
        algebraMap R S b6 * (d * algebraMap R S s) ^ 2 := by
  let c : Fin 3 → S := ![d * algebraMap R S s,
    d * f (WeierstrassIntegralChart.coord W 2 0),
    f (WeierstrassIntegralChart.coord W 2 1)]
  have hc0 : c 0 = d * algebraMap R S s := rfl
  have hc1 : c 1 = d * f (WeierstrassIntegralChart.coord W 2 0) := rfl
  have hc2 : c 2 = f (WeierstrassIntegralChart.coord W 2 1) := rfl
  have hi : aeval c (X 0 * X 2 - C s) = 0 := by
    simp only [map_sub, map_mul, aeval_X, aeval_C, hc0, hc2]
    linear_combination algebraMap R S s * hd
  have ho : aeval c (originalTransformPolynomial W) = 0 := by
    have he := WeierstrassIntegralChart.coord_equation W 2
    rw [Projective.equation_iff] at he
    have hm := congrArg f he
    simp only [map_sub, map_add, map_mul, map_pow, map_zero, AlgHom.commutes,
      map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, WeierstrassIntegralChart.coord_self,
      mul_one, one_pow] at hm
    have hxy : f (WeierstrassIntegralChart.coord W 2 1) *
        (d * f (WeierstrassIntegralChart.coord W 2 0)) =
          f (WeierstrassIntegralChart.coord W 2 0) := by rw [← mul_assoc, hd, one_mul]
    simpa only [originalTransformPolynomial, map_sub, map_add, map_mul, map_pow,
      aeval_X, aeval_C, hc1, hc2, hxy] using hm
  have he := congrArg (aeval c) (originalTransform_identity W s b3 b4 b6 h3 h4 h6)
  simp only [map_sub, map_mul, map_pow, aeval_X, hi, ho, zero_mul, sub_eq_zero] at he
  have hu := (isUnit_iff_exists_inv.mpr ⟨d, hd⟩).isRegular
  have hz : aeval c (equationPolynomial W b3 b4 b6) = 0 :=
    (hu.pow 2).left (he.symm.trans (mul_zero _).symm)
  simpa only [equationPolynomial, map_sub, map_add, map_mul, map_pow, map_one,
    aeval_X, aeval_C, hc0, hc1, hc2, sub_eq_zero] using hz

end FLT.Mazur.WeierstrassModificationY
