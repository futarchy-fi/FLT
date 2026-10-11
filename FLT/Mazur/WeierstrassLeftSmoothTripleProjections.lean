/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothTripleProduct
public import FLT.Mazur.WeierstrassSmoothTripleProjections
public import FLT.Mazur.WeierstrassIntegralTripleFlat

/-!
# Flat projections for two smooth inputs and an arbitrary third input

Reassociation exposes the last pair as a base change of the first smooth curve.
The first-pair projection is flat because the entire original cubic is flat;
no flatness of the enlarged addition is assumed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Forgetting the arbitrary third point is flat over every coefficient ring. -/
instance leftSmoothTriplePair_flat : Flat (leftSmoothTriplePair W) := by
  dsimp only [leftSmoothTriplePair]
  infer_instance

/-- Reassociate the actual triple to expose its smooth by whole last pair. -/
def leftSmoothTripleReassoc : leftSmoothTriple W ≅
    pullback (integralSmoothStructure W)
      (pullback.fst (integralSmoothStructure W) (integralCurveStructure W) ≫
        integralSmoothStructure W) :=
  pullback.congrHom pullback.condition rfl ≪≫
    pullbackAssoc (integralSmoothStructure W) (integralSmoothStructure W)
      (integralSmoothStructure W) (integralCurveStructure W)

/-- The last-pair projection is exactly the second reassociated projection. -/
theorem leftSmoothTripleLastPair_reassoc :
    leftSmoothTripleLastPair W = (leftSmoothTripleReassoc W).hom ≫ pullback.snd _ _ := by
  apply pullback.hom_ext <;>
    simp [leftSmoothTripleReassoc, leftSmoothTripleLastPair,
      leftSmoothTripleSecond, leftSmoothTripleThird, leftSmoothTriplePair,
      smoothFactorProductStructure]

/-- Forgetting the first smooth factor is smooth even over a singular third point. -/
instance leftSmoothTripleLastPair_smooth : Smooth (leftSmoothTripleLastPair W) := by
  rw [leftSmoothTripleLastPair_reassoc]
  infer_instance

/-- Projection to the first original smooth input is flat. -/
instance leftSmoothTripleFirst_flat : Flat (leftSmoothTripleFirst W) := by
  unfold leftSmoothTripleFirst
  infer_instance

/-- Projection to the second original smooth input is flat. -/
instance leftSmoothTripleSecond_flat : Flat (leftSmoothTripleSecond W) := by
  unfold leftSmoothTripleSecond
  infer_instance

/-- Projection to the arbitrary third input is smooth. -/
instance leftSmoothTripleThird_smooth : Smooth (leftSmoothTripleThird W) := by
  dsimp only [leftSmoothTripleThird]
  infer_instance

end FLT.Mazur.WeierstrassIntegralChart
