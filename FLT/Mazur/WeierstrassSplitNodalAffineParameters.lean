/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalUnitPoints

/-!
# Smooth affine nodal coordinates over arbitrary rings

On the intersection of the affine and smooth Y charts, the affine Y coordinate
is a unit. The cubic equation then forces X to be a unit and yields the slope
parametrization X=r(r+a), Y=r²(r+a), with both r and r+a invertible.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {S : Type*} [CommRing S]

/-- A unit Y coordinate forces the affine X coordinate to be a unit as well. -/
theorem splitNodalAffine_x_isUnit {a x y : S}
    (he : y ^ 2 + a * x * y = x ^ 3) (hy : IsUnit y) : IsUnit x := by
  have hh : x * (x ^ 2 - a * y) = y ^ 2 := by linear_combination -he
  exact isUnit_of_mul_isUnit_left (hh.symm ▸ hy.pow 2)

/-- The affine part of the smooth nodal chart has an actual unit slope parameter. -/
theorem splitNodalAffine_exists_parameter {a x y : S}
    (he : y ^ 2 + a * x * y = x ^ 3) (hy : IsUnit y) :
    ∃ r : Sˣ, IsUnit ((r : S) + a) ∧
      x = (r : S) * ((r : S) + a) ∧ y = (r : S) ^ 2 * ((r : S) + a) := by
  have hx := splitNodalAffine_x_isUnit he hy
  let r : Sˣ := hy.unit * hx.unit⁻¹
  have hr : (r : S) * x = y := by
    change ((hy.unit : S) * (↑(hx.unit⁻¹) : S)) * x = y
    rw [mul_assoc, Units.inv_mul_eq_one.mpr hx.unit_spec, mul_one, hy.unit_spec]
  have hxr : x = (r : S) * ((r : S) + a) := by
    apply (hx.pow 2).mul_right_inj.mp
    linear_combination -he - ((r : S) * x + y + a * x) * hr
  refine ⟨r, ?_, hxr, ?_⟩
  · exact isUnit_of_mul_isUnit_right (hxr ▸ hx)
  · rw [← hr, hxr]
    ring

/-- Every original affine chart algebra point satisfies the displayed nodal equation. -/
theorem splitNodalAffine_algebra_equation {R : Type*} [CommRing R] [Algebra R S]
    (a : Rˣ) (f : Coordinate (splitNodalEquation a) 2 →ₐ[R] S) :
    f (coord (splitNodalEquation a) 2 1) ^ 2 +
        algebraMap R S a * f (coord (splitNodalEquation a) 2 0) *
          f (coord (splitNodalEquation a) 2 1) =
      f (coord (splitNodalEquation a) 2 0) ^ 3 := by
  have h := projective_equation_of_hom (splitNodalEquation a) 2 f
  rw [WeierstrassCurve.Projective.equation_iff] at h
  simpa [splitNodalEquation, WeierstrassCurve.map, WeierstrassCurve.toProjective,
    Function.comp_def, sub_eq_zero] using h

end FLT.Mazur.WeierstrassIntegralChart
