/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSlopeLaurentGeometry
public import FLT.Mazur.WeierstrassAlgebraChartCross
public import FLT.Mazur.WeierstrassSplitNodalTorus

/-!
# The slope parameter retains the entire split nodal cubic map

The ordered Laurent ratio agrees with the affine cubic coordinates on the
whole slope localization, including nonreduced coefficient bases.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (a : Rˣ)
local notation "P" => SlopeOpen (a : R)
local notation "z" => slopeZ (a : R)
local notation "A" => algebraMap R P (a : R)
local notation "zi" => (Units.val ((IsUnit.unit (And.left (slope_units (a : R))))⁻¹) : P)
local notation "L" => slopeLaurentMap a

/-- The infinity horizontal coordinate is precisely the inverse slope. -/
theorem slopeLaurentMap_infinityX : L (splitNodalLaurentX a) = zi := by
  rw [splitNodalLaurentX, map_mul, AlgHom.commutes, slopeLaurentMap_sub_one,
    ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

/-- The entire affine vertical function cancels the normalized infinity coordinate. -/
theorem slopeLaurentMap_infinityZ :
    (z * (z + A) * z) * L (splitNodalLaurentZ a) = 1 := by
  apply ((LaurentPolynomial.isUnit_T (R := R) 1).map (L).toRingHom).mul_right_cancel
  change (z * (z + A) * z) * L (splitNodalLaurentZ a) *
    L (LaurentPolynomial.T 1) = 1 * L (LaurentPolynomial.T 1)
  have hz : z * zi = 1 := Units.mul_inv_eq_one.mpr (slope_units (a : R)).1.unit_spec
  have ht := congrArg L (splitNodalLaurent_relation a)
  rw [splitNodalLaurent_tangent, map_mul, map_pow, slopeLaurentMap_infinityX] at ht
  calc
    _ = (z * (z + A) * z) *
        (L (splitNodalLaurentZ a) * L (LaurentPolynomial.T 1)) := by ring
    _ = (z * (z + A) * z) * zi ^ 3 := by rw [ht]
    _ = (z * zi) ^ 2 * (z + A) * zi := by ring
    _ = 1 * L (LaurentPolynomial.T 1) := by rw [hz, one_pow, one_mul, slopeLaurentMap_T, one_mul]

/-- The torus parametrization keeps every function of an affine slope presentation. -/
theorem slopeLaurentMap_toCurve
    (f : WeierstrassIntegralChart.Coordinate (splitNodalEquation a) 2 →ₐ[R] P)
    (hx : f (coord (splitNodalEquation a) 2 0) = z * (z + A))
    (hy : f (coord (splitNodalEquation a) 2 1) = z * (z + A) * z) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ integralCurveChart (splitNodalEquation a) 2 =
      Spec.map (CommRingCat.ofHom (L).toRingHom) ≫ splitNodalTorusToCurve a := by
  change _ = Spec.map _ ≫ Spec.map _ ≫ integralCurveChart (splitNodalEquation a) 1
  rw [← Spec.map_comp_assoc]
  apply algebraChartCross_toCurve (splitNodalEquation a) 2 1 f
    ((L).comp (splitNodalChartToLaurent a))
  intro i
  rw [AlgHom.comp_apply, splitNodalChartToLaurent_coord]
  fin_cases i
  · change f (coord (splitNodalEquation a) 2 0) =
      f (coord (splitNodalEquation a) 2 1) * L (splitNodalLaurentX a)
    rw [hx, hy, slopeLaurentMap_infinityX, mul_assoc,
      Units.mul_inv_eq_one.mpr (slope_units (a : R)).1.unit_spec, mul_one]
  · change f (coord (splitNodalEquation a) 2 1) =
      f (coord (splitNodalEquation a) 2 1) * L 1
    rw [map_one, mul_one]
  · change f (coord (splitNodalEquation a) 2 2) =
      f (coord (splitNodalEquation a) 2 1) * L (splitNodalLaurentZ a)
    rw [coord_self, map_one, hy, slopeLaurentMap_infinityZ]

end FLT.Mazur.WeierstrassModificationX
