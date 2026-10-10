/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalUnitPoints
public import FLT.Mazur.EllipticSplitNodeGroup

/-!
# Comparing the Laurent coordinate with the classical nodal parameter

On the original Y chart, the inverse classical parameter is exactly 1+aX.
This fixes the orientation when comparing multiplication with cubic addition.
-/

@[expose] public noncomputable section

open WeierstrassCurve WeierstrassCurve.Projective

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {K : Type u} [Field K] (a : Kˣ)

/-- The chart tangent coordinate is the inverse of the older classical nodal parameter. -/
theorem splitNodalChart_classical_parameter
    (f : Coordinate (splitNodalEquation a) 1 →ₐ[K] K) :
    splitNodeParameter (a : K) (splitNodalChartProjective a f).toAffineLift =
      (1 + (a : K) * f (coord (splitNodalEquation a) 1 0))⁻¹ := by
  let x := f (coord (splitNodalEquation a) 1 0)
  let z := f (coord (splitNodalEquation a) 1 2)
  have hr : z * (1 + (a : K) * x) = x ^ 3 := by
    simpa only [map_mul, map_add, map_one, AlgHom.commutes, map_pow,
      Algebra.algebraMap_self, RingHom.id_apply] using congrArg f (splitNodalChart_relation a)
  have ht : 1 + (a : K) * x ≠ 0 := by
    have h := ((splitNodalTangentUnit a).isUnit.map f.toRingHom).ne_zero
    change f (1 + algebraMap K _ a * coord (splitNodalEquation a) 1 0) ≠ 0 at h
    simpa only [map_add, map_one, map_mul, AlgHom.commutes,
      Algebra.algebraMap_self, RingHom.id_apply] using h
  change splitNodeParameter (a : K)
    (Point.toAffine (splitNodeCurve (a : K)).toProjective
      (f ∘ coord (splitNodalEquation a) 1)) = _
  by_cases hz : z = 0
  · rw [Point.toAffine_of_Z_eq_zero hz]
    have hx : x = 0 := by
      apply (pow_eq_zero_iff (by decide : 3 ≠ 0)).mp
      simpa only [hz, zero_mul] using hr.symm
    simp [splitNodeParameter, hx, x]
  · have hn : (splitNodeCurve (a : K)).toProjective.Nonsingular
        (f ∘ coord (splitNodalEquation a) 1) := splitNodalChartPoint_nonsingular a f
    rw [Point.toAffine_of_Z_ne_zero hn hz]
    simp only [splitNodeParameter, Function.comp_apply, coord_self, map_one]
    change ((1 / z) / (x / z)) / ((1 / z) / (x / z) + (a : K)) = _
    have hx : x ≠ 0 := by
      intro hx
      exact (mul_ne_zero hz ht) (by simpa [hx] using hr)
    have he : (1 / z) / (x / z) = x⁻¹ := by field_simp
    rw [he]
    have hd : x⁻¹ + (a : K) ≠ 0 := by
      intro h
      apply ht
      simpa only [mul_add, mul_inv_cancel₀ hx, mul_zero, mul_comm x (a : K)] using
        congrArg (x * ·) h
    change x⁻¹ / (x⁻¹ + (a : K)) = (1 + (a : K) * x)⁻¹
    field_simp

/-- Unit evaluation has inverse classical parameter, including the point at infinity. -/
theorem splitNodalUnitPoint_classical_parameter (t : Kˣ) :
    splitNodeParameter (a : K) (splitNodalUnitPointEquiv a t).toAffineLift = (↑t : K)⁻¹ := by
  rw [show splitNodalUnitPointEquiv a t =
    splitNodalChartProjective a (splitNodalUnitChart a t) from rfl,
    splitNodalChart_classical_parameter]
  congr 1
  change 1 + (a : K) * LaurentUnitPoints.evalUnit t
    (splitNodalChartToLaurent a (coord (splitNodalEquation a) 1 0)) = _
  have h := congrArg (LaurentUnitPoints.evalUnit (R := K) t) (splitNodalChartToLaurent_tangent a)
  simpa only [map_add, map_one, map_mul, AlgHom.commutes, Algebra.algebraMap_self,
    RingHom.id_apply, LaurentUnitPoints.evalUnit_T, zpow_one] using h

end FLT.Mazur.WeierstrassIntegralChart
