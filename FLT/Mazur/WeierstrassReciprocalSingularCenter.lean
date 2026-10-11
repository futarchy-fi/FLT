/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalCubicSpecialization
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The singular center misses the reciprocal output charts

The singular origin has Y-coordinate zero. Neither reciprocal output-Y chart
can contain it, even after a nonreduced specialization. Thus the original
center ideal restricts to the unit ideal on both reciprocal domains.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve WeierstrassIntegralAddition
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- A reciprocal output-Y chart over the singular origin is the zero ring. -/
theorem reciprocalSpecialization_singular_origin (b : Bool)
    (f : additionChartRing W (reciprocalIndex b) →ₐ[R] S)
    (h3 : algebraMap R S W.a₃ = 0) (h4 : algebraMap R S W.a₄ = 0)
    (hx : f (reciprocalInputRight W b (coord W 2 0)) = 0)
    (hy : f (reciprocalInputRight W b (coord W 2 1)) = 0) : (1 : S) = 0 := by
  let x := f (reciprocalInputLeft W b (coord W 2 0))
  let y := f (reciprocalInputLeft W b (coord W 2 1))
  let m := f (reciprocalChartSlope W b)
  let V := W.map (algebraMap R S)
  have hl : m * y = x := by
    simpa only [hx, hy, sub_zero] using reciprocalSpecialization_line W b f
  have hc : m * (x ^ 2 + V.a₂ * x - V.a₁ * y) = y := by
    simpa only [hx, hy, WeierstrassCurve.toAffine, map_a₃, map_a₄, h3, h4,
      mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0)] using
      reciprocalSpecialization_cubic W b f
  have hu : IsUnit y := by
    have hd := reciprocalSpecialization_denominator_unit W b f
    simp only [hx, hy, WeierstrassCurve.toAffine, map_a₄, h4,
      mul_zero, add_zero, sub_zero, zero_pow (by decide : 2 ≠ 0)] at hd
    rcases hd with hd | hd
    · exact hd
    · have he : x ^ 2 + V.a₂ * x - V.a₁ * y =
          y * (m * x + V.a₂ * m - V.a₁) := by
        linear_combination -(x + V.a₂) * hl
      rw [he] at hd
      exact isUnit_of_mul_isUnit_left hd
  have hh : reciprocalH V x 0 m = 0 := by
    apply hu.mul_left_cancel
    dsimp only [reciprocalH]
    linear_combination -hc - m * (x + V.a₂) * hl
  have ho : reciprocalXYZ V x 0 y m 1 = 0 := by
    simp only [reciprocalXYZ, Matrix.cons_val_one, Matrix.cons_val_zero,
      show V.a₃ = 0 from h3, hh, mul_zero, add_zero]
    linear_combination -m ^ 2 * hl
  have hn := reciprocalSpecialization_coord W b f 1
  rw [coord_self, map_one, map_one, hx] at hn
  change 1 = f (reciprocalChartInverse W b) * reciprocalXYZ V x 0 y m 1 at hn
  rw [ho, mul_zero] at hn
  exact hn

/-- Any ideal containing the input center data is the unit ideal on a reciprocal domain. -/
theorem reciprocalSpecialization_center_eq_top (b : Bool)
    (f : additionChartRing W (reciprocalIndex b) →ₐ[R] S) (I : Ideal S)
    (h3 : algebraMap R S W.a₃ ∈ I) (h4 : algebraMap R S W.a₄ ∈ I)
    (hx : f (reciprocalInputRight W b (coord W 2 0)) ∈ I)
    (hy : f (reciprocalInputRight W b (coord W 2 1)) ∈ I) : I = ⊤ := by
  let q : S →ₐ[R] S ⧸ I := Ideal.Quotient.mkₐ R I
  have h := reciprocalSpecialization_singular_origin W b (q.comp f)
    (by
      rw [IsScalarTower.algebraMap_apply R S (S ⧸ I)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h3)
    (by
      rw [IsScalarTower.algebraMap_apply R S (S ⧸ I)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h4)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hx) (Ideal.Quotient.eq_zero_iff_mem.mpr hy)
  apply (Ideal.eq_top_iff_one I).mpr
  exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_one] using h)

end FLT.Mazur.WeierstrassIntegralChart
