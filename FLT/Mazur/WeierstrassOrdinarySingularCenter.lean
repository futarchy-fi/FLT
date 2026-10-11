/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassOrdinaryChartSpecialization

/-!
# Ordinary addition fixes the scheme-theoretic singular origin

When the second input and the coefficients a3 and a4 vanish, the actual ordinary
chart output has both affine coordinates zero. The proof works over every
commutative ring, retaining nilpotents for subsequent center-ideal calculations.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- The second ordinary chart has its actual tangent denominator invertible. -/
theorem ordinarySpecialization_tangent_unit
    (f : additionChartRing W (ordinaryIndex true) →ₐ[R] S) :
    IsUnit (f (ordinaryInputLeft W true (coord W 2 1)) +
      f (ordinaryInputRight W true (coord W 2 1)) +
      algebraMap R S W.a₁ * f (ordinaryInputRight W true (coord W 2 0)) +
      algebraMap R S W.a₃) := by
  simpa only [ordinaryInputLeft, ordinaryInputRight, AlgHom.comp_apply,
    productX₂, productY₁, productY₂, Bool.true_eq, ite_true, tangentDenominator,
    map_add, map_mul, AlgHom.commutes] using (ordinaryChartDenominator_isUnit W true).map f

/-- Both original ordinary charts fix the singular origin over arbitrary coefficient algebras. -/
theorem ordinarySpecialization_singular_origin (b : Bool)
    (f : additionChartRing W (ordinaryIndex b) →ₐ[R] S)
    (h3 : algebraMap R S W.a₃ = 0) (h4 : algebraMap R S W.a₄ = 0)
    (hx : f (ordinaryInputRight W b (coord W 2 0)) = 0)
    (hy : f (ordinaryInputRight W b (coord W 2 1)) = 0) :
    f (ordinaryChartAddition W b (coord W 2 0)) = 0 ∧
      f (ordinaryChartAddition W b (coord W 2 1)) = 0 := by
  let x := f (ordinaryInputLeft W b (coord W 2 0))
  let y := f (ordinaryInputLeft W b (coord W 2 1))
  let l := f (ordinaryChartSlope W b)
  let V := (W.map (algebraMap R S)).toAffine
  have hl : l * x = y := by
    simpa only [hx, hy, sub_zero] using ordinarySpecialization_line W b f
  have hc : l * y = x ^ 2 + V.a₂ * x - V.a₁ * y := by
    simpa only [hx, hy, WeierstrassCurve.toAffine, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, h3, h4, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0)]
      using ordinarySpecialization_cubic W b f
  have hu : IsUnit x := by
    cases b
    · simpa only [x, hx, sub_zero] using ordinarySpecialization_secant_unit W f
    · have hyu : IsUnit y := by
        simpa only [y, hx, hy, h3, mul_zero, add_zero] using
          ordinarySpecialization_tangent_unit W f
      exact isUnit_of_mul_isUnit_right (hl.symm ▸ hyu)
  have ho : V.addX x 0 l = 0 := by
    apply hu.mul_left_cancel
    simp only [Affine.addX, sub_zero, mul_zero]
    linear_combination hc + (l + V.a₁) * hl
  constructor
  · simpa only [ordinarySpecialization_coord, Matrix.cons_val_zero, hx] using ho
  · have ho' : V.addY x 0 y l = 0 := by
      simp only [Affine.addY, Affine.negAddY, Affine.negY, ho,
        show V.a₃ = 0 from h3]
      linear_combination hl
    simpa only [ordinarySpecialization_coord, Matrix.cons_val_one,
      Matrix.cons_val_zero, hx] using ho'

end FLT.Mazur.WeierstrassIntegralChart
