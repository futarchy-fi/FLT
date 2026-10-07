/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTransportedOrdinary
public import FLT.Mazur.WeierstrassInfinityTransportedReciprocal
public import FLT.Mazur.WeierstrassAffinePolynomialIntersections

/-!
# Full-domain infinity comparison for all four transported affine charts

Every actual intersection has an output-overlap map whose two projections
are the existing affine and infinity addition laws. This includes the
polynomial base locus; the proof never localizes at a polynomial output.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (b : Bool)

/-- The equal reciprocal outputs factor through the self-overlap of the Y chart. -/
def infinityTransportedReciprocalOutputLift :
    Overlap W 1 1 →ₐ[R] InfinityTransportedIntersection W (reciprocalIndex b) :=
  scaledChartLift W 1 1 (infinityTransportedAddition W (reciprocalIndex b))
    ((infinityTransportedChart W (reciprocalIndex b)).comp (reciprocalChartAddition W b))
    1 isUnit_one (fun a => by
      rw [infinityTransported_reciprocal_addition, one_mul])

/-- The self-overlap retains reciprocal addition. -/
theorem infinityTransportedReciprocalOutputLift_restriction :
    (infinityTransportedReciprocalOutputLift W b).comp (overlapRestriction W 1 1) =
      (infinityTransportedChart W (reciprocalIndex b)).comp (reciprocalChartAddition W b) :=
  scaledChartLift_restriction ..

/-- The self-overlap also retains infinity addition. -/
theorem infinityTransportedReciprocalOutputLift_transition :
    (infinityTransportedReciprocalOutputLift W b).comp (transitionBase W 1 1) =
      infinityTransportedAddition W (reciprocalIndex b) := scaledChartLift_transition ..

variable (i : AdditionChartIndex)

/-- Actual output-overlap factorization for each of the four full intersections. -/
def infinityTransportedOutputLift :
    Overlap W (additionChartOutput i) 1 →ₐ[R] InfinityTransportedIntersection W i :=
  match i with
  | .secant => infinityTransportedOrdinaryOutputLift W false
  | .tangent => infinityTransportedOrdinaryOutputLift W true
  | .verticalSecant => infinityTransportedReciprocalOutputLift W false
  | .verticalTangent => infinityTransportedReciprocalOutputLift W true

/-- The first overlap projection is the existing transported affine addition law. -/
theorem infinityTransportedOutputLift_restriction :
    (infinityTransportedOutputLift W i).comp (overlapRestriction W (additionChartOutput i) 1) =
      (infinityTransportedChart W i).comp (additionChartAlgOutput W i) := by
  cases i
  · exact infinityTransportedOrdinaryOutputLift_restriction W false
  · exact infinityTransportedOrdinaryOutputLift_restriction W true
  · exact infinityTransportedReciprocalOutputLift_restriction W false
  · exact infinityTransportedReciprocalOutputLift_restriction W true

/-- The output transition is the existing infinity addition law. -/
theorem infinityTransportedOutputLift_transition :
    (infinityTransportedOutputLift W i).comp (transitionBase W (additionChartOutput i) 1) =
      infinityTransportedAddition W i := by
  cases i
  · exact infinityTransportedOrdinaryOutputLift_transition W false
  · exact infinityTransportedOrdinaryOutputLift_transition W true
  · exact infinityTransportedReciprocalOutputLift_transition W false
  · exact infinityTransportedReciprocalOutputLift_transition W true

open AlgebraicGeometry CategoryTheory

/-- The affine output on the actual intersection spectrum factors through its output overlap. -/
theorem infinityTransportedOutputLift_spec_affine :
    Spec.map (CommRingCat.ofHom (infinityTransportedOutputLift W i).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (overlapRestriction W (additionChartOutput i) 1).toRingHom) =
      Spec.map (CommRingCat.ofHom (infinityTransportedAffine W i).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (transportedAdditionAffine W 1 1 i).toRingHom) ≫
          additionChartSpec W i := by
  rw [← additionChartAlgOutput_spec, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (infinityTransportedOutputLift_restriction W i)

/-- The other output projection on the full intersection spectrum is infinity addition. -/
theorem infinityTransportedOutputLift_spec_infinity :
    Spec.map (CommRingCat.ofHom (infinityTransportedOutputLift W i).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (transitionBase W (additionChartOutput i) 1).toRingHom) =
      Spec.map (CommRingCat.ofHom (infinityTransportedInfinity W i).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (infinityAdditionChart W).toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (infinityTransportedOutputLift_transition W i)

end FLT.Mazur.WeierstrassIntegralChart
