/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineCoordinateFlat
public import FLT.Mazur.WeierstrassInfinityProductFlat
public import FLT.Mazur.WeierstrassIntegralTripleProduct
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc

/-!
# Flat original-input projections on the whole integral triple product

Both affine charts are flat over the coefficient ring, hence so is the glued
curve. Pullback reassociation proves flatness of the last-pair projection
without any flatness assertion about the addition morphism.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The actual affine chart is flat over the base spectrum. -/
instance affineChartStructure_flat : Flat (chartStructure W 2) :=
  Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr (affineChart_flat W))

/-- Flatness of the two actual charts descends to the entire integral cubic. -/
instance integralCurveStructure_flat : Flat (integralCurveStructure W) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover (integralCurveTwoChartCover W)).mpr
  intro b
  change Bool at b
  change Flat (integralCurveChart W (if b then 1 else 2) ≫ integralCurveStructure W)
  rw [integralCurveChart_structure]
  cases b
  · exact affineChartStructure_flat W
  · exact infinityChartStructure_flat W

/-- The curve product is flat over the coefficient spectrum. -/
instance integralCurveProductStructure_flat : Flat (integralCurveProductStructure W) := by
  unfold integralCurveProductStructure
  infer_instance

/-- The first-pair projection omits one flat curve factor. -/
instance integralCurveTriplePair_flat : Flat (integralCurveTriplePair W) := by
  dsimp only [integralCurveTriplePair]
  infer_instance

/-- Reassociate the actual triple product to expose its last two factors. -/
def integralCurveTripleReassoc : integralCurveTriple W ≅
    pullback (integralCurveStructure W)
      (pullback.fst (integralCurveStructure W) (integralCurveStructure W) ≫
        integralCurveStructure W) :=
  pullback.congrHom pullback.condition rfl ≪≫
    pullbackAssoc (integralCurveStructure W) (integralCurveStructure W)
      (integralCurveStructure W) (integralCurveStructure W)

/-- The actual last-pair projection is the reassociated second projection. -/
theorem integralCurveTripleLastPair_reassoc :
    integralCurveTripleLastPair W = (integralCurveTripleReassoc W).hom ≫ pullback.snd _ _ := by
  apply pullback.hom_ext <;>
    simp [integralCurveTripleReassoc, integralCurveTripleLastPair,
      integralCurveTripleSecond, integralCurveTripleThird, integralCurveTriplePair,
      integralCurveProductStructure]

/-- The last-pair projection is flat as a base change of the first curve factor. -/
instance integralCurveTripleLastPair_flat : Flat (integralCurveTripleLastPair W) := by
  rw [integralCurveTripleLastPair_reassoc]
  infer_instance

/-- The first original input projection is flat. -/
instance integralCurveTripleFirst_flat : Flat (integralCurveTripleFirst W) := by
  unfold integralCurveTripleFirst
  infer_instance

/-- The middle original input projection is flat. -/
instance integralCurveTripleSecond_flat : Flat (integralCurveTripleSecond W) := by
  unfold integralCurveTripleSecond
  infer_instance

/-- The final original input projection is flat. -/
instance integralCurveTripleThird_flat : Flat (integralCurveTripleThird W) := by
  dsimp only [integralCurveTripleThird]
  infer_instance

end FLT.Mazur.WeierstrassIntegralChart
