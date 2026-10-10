/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassProjectiveChartProduct
public import FLT.Mazur.WeierstrassChartOverlap

/-!
# Coefficient extension on the integral cubic charts

The universal normalized coordinates define the actual chart map after any
coefficient extension. The maps extend across principal overlaps and retain
the inverse coordinate used by the normalization transitions.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- The universal point after coefficient extension still solves the original cubic. -/
theorem coefficient_coord_equation (j : Fin 3) :
    (W.map (algebraMap R (Coordinate (W.map (algebraMap R S)) j))).toProjective.Equation
      (coord (W.map (algebraMap R S)) j) := by
  simpa only [WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq] using
    coord_equation (W.map (algebraMap R S)) j

/-- The original chart algebra maps to the coefficient-extended chart. -/
def chartCoefficientMap (j : Fin 3) :
    Coordinate W j →ₐ[R] Coordinate (W.map (algebraMap R S)) j :=
  evaluation W j (coord (W.map (algebraMap R S)) j)
    (coefficient_coord_equation W j) (coord_self _ j)

/-- Coefficient extension retains each universal normalized coordinate. -/
@[simp] theorem chartCoefficientMap_coord (j i : Fin 3) :
    chartCoefficientMap (S := S) W j (coord W j i) = coord (W.map (algebraMap R S)) j i :=
  evaluation_coord W j _ _ _ i

/-- Coefficient extension on the source chart, followed by localization. -/
def overlapCoefficientBase (j k : Fin 3) :
    Coordinate W j →ₐ[R] Overlap (W.map (algebraMap R S)) j k :=
  (IsScalarTower.toAlgHom R (Coordinate (W.map (algebraMap R S)) j)
    (Overlap (W.map (algebraMap R S)) j k)).comp (chartCoefficientMap W j)

/-- Its second normalizing coordinate is invertible on the new overlap. -/
theorem overlapCoefficientBase_isUnit (j k : Fin 3) :
    IsUnit (overlapCoefficientBase (S := S) W j k (coord W j k)) := by
  change IsUnit (algebraMap _ (Overlap (W.map (algebraMap R S)) j k)
    (chartCoefficientMap (S := S) W j (coord W j k)))
  rw [chartCoefficientMap_coord]
  exact overlapCoord_isUnit _ j k

/-- The actual coefficient extension of principal overlap algebras. -/
def overlapCoefficientMap (j k : Fin 3) :
    Overlap W j k →ₐ[R] Overlap (W.map (algebraMap R S)) j k :=
  IsLocalization.Away.liftAlgHom (coord W j k) (overlapCoefficientBase_isUnit W j k)

/-- Coefficient extension preserves all overlap coordinates. -/
@[simp] theorem overlapCoefficientMap_coord (j k i : Fin 3) :
    overlapCoefficientMap (S := S) W j k (overlapCoord W j k i) =
      overlapCoord (W.map (algebraMap R S)) j k i := by
  change IsLocalization.Away.lift (coord W j k) (overlapCoefficientBase_isUnit W j k)
    (algebraMap _ _ (coord W j i)) = _
  rw [IsLocalization.Away.lift_eq]
  change algebraMap _ (Overlap (W.map (algebraMap R S)) j k)
    (chartCoefficientMap (S := S) W j (coord W j i)) = _
  rw [chartCoefficientMap_coord]
  rfl

/-- The normalization inverse is natural under arbitrary coefficient extension. -/
@[simp] theorem overlapCoefficientMap_inverse (j k : Fin 3) :
    overlapCoefficientMap (S := S) W j k (overlapInverse W j k) =
      overlapInverse (W.map (algebraMap R S)) j k := by
  apply (overlapCoord_isUnit (W.map (algebraMap R S)) j k).mul_right_cancel
  rw [← overlapCoefficientMap_coord W j k k, ← map_mul, overlapInverse_mul, map_one,
    overlapCoefficientMap_coord, overlapInverse_mul]

end FLT.Mazur.WeierstrassIntegralChart
