/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityNegationChart
public import FLT.Mazur.WeierstrassScaledChartComparison

/-!
# Comparing affine and infinity negation on their overlap

After changing input charts the two formulas differ by an explicit unit.
Their outputs therefore factor through the actual Y/Z chart overlap, with
both prescribed restrictions. No density or reducedness argument is used.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- Affine negation after chart transition is the normalized homogeneous negation. -/
theorem affineNegation_transition_coord (i : Fin 3) :
    transitionBase W 1 2 (affineNegation W (coord W 2 i)) =
      overlapInverse W 1 2 * overlapRestriction W 1 2 (chartNegationCoordinates W 1 i) := by
  fin_cases i
  · change transitionBase W 1 2 (affineNegation W (coord W 2 0)) = _
    rw [affineNegation_x, transitionBase_coord]
    rfl
  · change transitionBase W 1 2 (affineNegation W (coord W 2 1)) = _
    rw [affineNegation_y]
    simp only [map_sub, map_neg, map_mul, AlgHom.commutes, transitionBase_coord]
    change -(_ * overlapCoord W 1 2 1) - algebraMap R _ W.a₁ *
      (_ * overlapCoord W 1 2 0) - algebraMap R _ W.a₃ =
        _ * overlapRestriction W 1 2
          (-coord W 1 1 - algebraMap R _ W.a₁ * coord W 1 0 -
            algebraMap R _ W.a₃ * coord W 1 2)
    simp only [map_sub, map_neg, map_mul, AlgHom.commutes]
    change -(_ * overlapCoord W 1 2 1) - algebraMap R _ W.a₁ *
      (_ * overlapCoord W 1 2 0) - algebraMap R _ W.a₃ =
        _ * (-overlapCoord W 1 2 1 - algebraMap R _ W.a₁ * overlapCoord W 1 2 0 -
          algebraMap R _ W.a₃ * overlapCoord W 1 2 2)
    linear_combination algebraMap R _ W.a₃ * overlapInverse_mul W 1 2
  · change transitionBase W 1 2 (affineNegation W (coord W 2 2)) =
      overlapInverse W 1 2 * overlapCoord W 1 2 2
    rw [coord_self, map_one, map_one, overlapInverse_mul]

variable (f : InfinityNegationOpen W →ₐ[R] S) (g : Overlap W 1 2 →ₐ[R] S)
  (h : f.comp (infinityNegationRestriction W) = g.comp (overlapRestriction W 1 2))

/-- The comparison factor between normalized Y and Z outputs. -/
def negationOverlapScale : S :=
  f (infinityNegationInverse W) * g (overlapCoord W 1 2 2)

/-- Both factors of the comparison scale are invertible on the common domain. -/
theorem negationOverlapScale_isUnit : IsUnit (negationOverlapScale W f g) :=
  ((Units.isUnit (infinityNegationDen_isUnit W).unit⁻¹).map f).mul
    ((overlapCoord_isUnit W 1 2).map g)

include h in
/-- The two normalized negation outputs have exactly the common unit factor. -/
theorem negationOverlap_scaled (i : Fin 3) :
    (f.comp (infinityNegationChart W)) (coord W 1 i) =
      negationOverlapScale W f g *
        ((g.comp (transitionBase W 1 2)).comp (affineNegation W)) (coord W 2 i) := by
  simp only [AlgHom.comp_apply, infinityNegationChart_coord, affineNegation_transition_coord,
    map_mul, negationOverlapScale]
  have hi := DFunLike.congr_fun h (chartNegationCoordinates W 1 i)
  change f (infinityNegationRestriction W _) = g (overlapRestriction W 1 2 _) at hi
  rw [hi]
  have hz := congrArg g (overlapInverse_mul W 1 2)
  rw [map_mul, map_one] at hz
  linear_combination -f (infinityNegationInverse W) *
    g (overlapRestriction W 1 2 (chartNegationCoordinates W 1 i)) * hz

/-- The common negation output lies in the actual Y/Z overlap. -/
def negationOverlapLift : Overlap W 1 2 →ₐ[R] S :=
  scaledChartLift W 2 1 ((g.comp (transitionBase W 1 2)).comp (affineNegation W))
    (f.comp (infinityNegationChart W)) (negationOverlapScale W f g)
    (negationOverlapScale_isUnit W f g) (negationOverlap_scaled W f g h)

/-- Restricting the output overlap to Y recovers the infinity formula. -/
theorem negationOverlapLift_restriction :
    (negationOverlapLift W f g h).comp (overlapRestriction W 1 2) =
      f.comp (infinityNegationChart W) := scaledChartLift_restriction ..

/-- Changing the output to Z recovers the original affine negation formula. -/
theorem negationOverlapLift_transition :
    (negationOverlapLift W f g h).comp (transitionBase W 1 2) =
      (g.comp (transitionBase W 1 2)).comp (affineNegation W) :=
  scaledChartLift_transition ..

end FLT.Mazur.WeierstrassIntegralChart
