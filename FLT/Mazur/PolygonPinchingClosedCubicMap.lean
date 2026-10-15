/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonPinchingCompleteCubicContraction
import all FLT.Mazur.PolygonPinchingCompleteClosedComparison
import all FLT.Mazur.PolygonPinchingCompleteCubicContraction

/-!
# The original complete cubic map on the entire closed pullback

Use the actual Cartesian change of the original complete-family cubic map.
The pinching comparison identifies it with the geometric contraction and
the whole closed-cubic isomorphism, including the singular node.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching PolygonOneGonContraction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeClosedFiberInclusion
variable (K : Type) [Field K] (n : ℕ) (hn : 2 ≤ n) [NeZero n]
local notation "π" => exactVeroneseProjToBase K n hn
local notation "s" => completeClosedBase K

/-- The original cubic contraction after the actual closed-point Cartesian base change. -/
def completeClosedPullbackCubicMap (i : Fin n) :
    pullback π s ⟶ (closedPointCubicOver K n hn i).left :=
  completePointToCubicBaseChange K n hn s (pullback.fst π s) (pullback.snd π s)
    (IsPullback.of_hasPullback π s) i

/-- Inclusion into the original complete cubic retains its original contraction. -/
@[reassoc] theorem completeClosedPullbackCubicMap_inclusion (i : Fin n) :
    completeClosedPullbackCubicMap K n hn i ≫ completePointCubicClosedInclusion K n hn i =
      pullback.fst π s ≫ completePointToIntegralCubic K n hn i :=
  completePointToCubicBaseChange_fst K n hn s _ _ (IsPullback.of_hasPullback π s) i

variable {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (hp : IsPushout (toComponents K n (by omega)) (toNodes K n) p q) (i : Fin n)

/-- The entire original base-changed cubic map is precisely the pinching contraction. -/
@[reassoc] theorem pinchingCompleteClosedIso_closedCubic :
    (pinchingCompleteClosedIso K n hn p q hp).hom ≫ completeClosedPullbackCubicMap K n hn i =
      (contraction K n (by omega) p q hp i).left ≫
        (closedPointContractionCubicIso K n hn i).hom := by
  apply (cancel_mono (completePointCubicClosedInclusion K n hn i)).mp
  simp only [Category.assoc, completeClosedPullbackCubicMap_inclusion]
  exact pinchingCompleteClosedIso_cubic K n hn p q hp i

end FLT.Mazur.PolygonInfinitesimalStages
