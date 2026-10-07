/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTransportedOutput
public import FLT.Mazur.WeierstrassScaledChartComparison

/-!
# Ordinary and infinity addition through the actual output overlap

The full-domain homogeneous comparison has a unit factor. It therefore
constructs an output-overlap map recovering both existing addition maps,
including at diagonal points in the polynomial base locus.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (b : Bool)

/-- The ordinary affine addition map on the full intersection. -/
def infinityTransportedOrdinaryAddition :
    Coordinate W 2 →ₐ[R] InfinityTransportedIntersection W (ordinaryIndex b) :=
  (infinityTransportedChart W (ordinaryIndex b)).comp (ordinaryChartAddition W b)

/-- Unit relating the two existing normalized chart maps. -/
def infinityTransportedOrdinaryScale : InfinityTransportedIntersection W (ordinaryIndex b) :=
  ↑(infinityTransportedInputFactor_isUnit W (ordinaryIndex b)).unit⁻¹ *
    infinityTransportedOrdinaryIntercept W b ^ 3 *
      infinityTransportedCoordinates W (ordinaryIndex b) 1

/-- The comparison scale is invertible without removing the polynomial base locus. -/
theorem infinityTransportedOrdinaryScale_isUnit : IsUnit (infinityTransportedOrdinaryScale W b) :=
  ((Units.isUnit _).mul ((infinityTransported_ordinary_intercept_isUnit W b).pow 3)).mul
    (infinityTransportedCoordinates_y_isUnit W (ordinaryIndex b))

/-- Every coordinate of the normalized ordinary map has the same unit comparison factor. -/
theorem infinityTransported_ordinary_scaled (a : Fin 3) :
    infinityTransportedOrdinaryAddition W b (coord W 2 a) =
      infinityTransportedOrdinaryScale W b *
        infinityTransportedAddition W (ordinaryIndex b) (coord W 1 a) := by
  have hi : ↑(infinityTransportedInputFactor_isUnit W (ordinaryIndex b)).unit⁻¹ *
      infinityTransportedInputFactor W (ordinaryIndex b) = 1 :=
    Units.inv_mul_eq_one.mpr (infinityTransportedInputFactor_isUnit W (ordinaryIndex b)).unit_spec
  have ho := infinityTransported_ordinary_output W b a
  have hn := infinityTransportedAddition_mul W (ordinaryIndex b) a
  dsimp only [infinityTransportedOrdinaryAddition, infinityTransportedOrdinaryScale,
    AlgHom.comp_apply]
  linear_combination
    -↑(infinityTransportedInputFactor_isUnit W (ordinaryIndex b)).unit⁻¹ * ho -
    ↑(infinityTransportedInputFactor_isUnit W (ordinaryIndex b)).unit⁻¹ *
      infinityTransportedOrdinaryIntercept W b ^ 3 * hn -
    infinityTransportedChart W (ordinaryIndex b) (ordinaryChartAddition W b (coord W 2 a)) * hi

/-- Both addition laws factor through their actual output overlap on the full intersection. -/
def infinityTransportedOrdinaryOutputLift :
    Overlap W 2 1 →ₐ[R] InfinityTransportedIntersection W (ordinaryIndex b) :=
  scaledChartLift W 1 2 (infinityTransportedAddition W (ordinaryIndex b))
    (infinityTransportedOrdinaryAddition W b) (infinityTransportedOrdinaryScale W b)
    (infinityTransportedOrdinaryScale_isUnit W b) (infinityTransported_ordinary_scaled W b)

/-- The overlap restriction retains the existing ordinary addition morphism. -/
theorem infinityTransportedOrdinaryOutputLift_restriction :
    (infinityTransportedOrdinaryOutputLift W b).comp (overlapRestriction W 2 1) =
      infinityTransportedOrdinaryAddition W b := scaledChartLift_restriction ..

/-- The output transition retains the existing infinity addition morphism. -/
theorem infinityTransportedOrdinaryOutputLift_transition :
    (infinityTransportedOrdinaryOutputLift W b).comp (transitionBase W 2 1) =
      infinityTransportedAddition W (ordinaryIndex b) := scaledChartLift_transition ..

end FLT.Mazur.WeierstrassIntegralChart
