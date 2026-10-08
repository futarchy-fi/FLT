/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothTripleProduct
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc

/-!
# Smooth original-input projections on the smooth triple product

Both pair projections and all three original-input projections are smooth,
hence flat. Reassociation exposes the last pair as a base change; no
flatness or associativity of addition is assumed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The curve product is smooth over the coefficient spectrum. -/
instance smoothFactorProductStructure_smooth : Smooth (smoothFactorProductStructure W) := by
  unfold smoothFactorProductStructure
  infer_instance

/-- The first-pair projection omits one smooth curve factor. -/
instance smoothFactorTriplePair_smooth : Smooth (smoothFactorTriplePair W) := by
  dsimp only [smoothFactorTriplePair]
  infer_instance

/-- Reassociate the actual triple product to expose its last two factors. -/
def smoothFactorTripleReassoc : smoothFactorTriple W ≅
    pullback (integralSmoothStructure W)
      (pullback.fst (integralSmoothStructure W) (integralSmoothStructure W) ≫
        integralSmoothStructure W) :=
  pullback.congrHom pullback.condition rfl ≪≫
    pullbackAssoc (integralSmoothStructure W) (integralSmoothStructure W)
      (integralSmoothStructure W) (integralSmoothStructure W)

/-- The actual last-pair projection is the reassociated second projection. -/
theorem smoothFactorTripleLastPair_reassoc :
    smoothFactorTripleLastPair W = (smoothFactorTripleReassoc W).hom ≫ pullback.snd _ _ := by
  apply pullback.hom_ext <;>
    simp [smoothFactorTripleReassoc, smoothFactorTripleLastPair,
      smoothFactorTripleSecond, smoothFactorTripleThird, smoothFactorTriplePair,
      smoothFactorProductStructure]

/-- The last-pair projection is smooth as a base change of the first curve factor. -/
instance smoothFactorTripleLastPair_smooth : Smooth (smoothFactorTripleLastPair W) := by
  rw [smoothFactorTripleLastPair_reassoc]
  infer_instance

/-- The first original input projection is smooth. -/
instance smoothFactorTripleFirst_smooth : Smooth (smoothFactorTripleFirst W) := by
  unfold smoothFactorTripleFirst
  infer_instance

/-- The middle original input projection is smooth. -/
instance smoothFactorTripleSecond_smooth : Smooth (smoothFactorTripleSecond W) := by
  unfold smoothFactorTripleSecond
  infer_instance

/-- The final original input projection is smooth. -/
instance smoothFactorTripleThird_smooth : Smooth (smoothFactorTripleThird W) := by
  dsimp only [smoothFactorTripleThird]
  infer_instance

end FLT.Mazur.WeierstrassIntegralChart
