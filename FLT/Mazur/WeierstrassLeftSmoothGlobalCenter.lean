/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothInputCenter
public import FLT.Mazur.WeierstrassLeftSmoothFactorAddition

/-!
# Full center containment for the global integral action

The four original projective input charts detect containment of actual ideal
sheaves. The resulting statement is transported to the unchanged smooth by
whole-cubic product and hence to arbitrary scheme-valued inputs.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.IdealSheafData
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s * b6)

include h3 h4 h6

/-- The original global glued action preserves the full center ideal. -/
theorem leftSmoothCurveAddition_center_le :
    (modificationCenterSheaf W s).comap (leftSmoothCurveAddition W) ≤
      (modificationCenterSheaf W s).comap
        ((leftSmoothCurveProductOpen W).ι ≫
          pullback.snd (integralCurveStructure W) (integralCurveStructure W)) := by
  apply BaseAdicThickening.idealSheaf_le_of_openCover (leftSmoothCurveProductCover W)
  rintro ⟨b, c⟩
  have h := comap_mono (leftSmoothCurveProductCoverToChart W b c)
    (leftSmoothInputAddition_center_le W s b3 b4 b6 h3 h4 h6 b c)
  simpa only [← comap_comp, ← leftSmoothCurveProductCover_addition,
    ← Category.assoc, leftSmoothCurveProductCoverToChart_inputs] using h

/-- The actual smooth by whole-cubic action has the same full ideal containment. -/
theorem leftSmoothFactorAddition_center_le :
    (modificationCenterSheaf W s).comap (leftSmoothFactorAddition W) ≤
      (modificationCenterSheaf W s).comap
        (pullback.snd (integralSmoothStructure W) (integralCurveStructure W)) := by
  have h := comap_mono (leftSmoothFactorsToProduct W)
    (leftSmoothCurveAddition_center_le W s b3 b4 b6 h3 h4 h6)
  simpa only [← comap_comp, ← Category.assoc, leftSmoothFactorsToProduct_inclusion,
    leftSmoothFactorsInclusion, pullback.lift_snd, leftSmoothFactorAddition] using h

/-- Every actual smooth translation preserves the full center on every scheme of points. -/
theorem leftSmoothPointAddition_center_le {X : Scheme.{u}}
    (a : X ⟶ (integralSmoothOpen W).toScheme) (b : X ⟶ integralCurve W)
    (h : a ≫ integralSmoothStructure W = b ≫ integralCurveStructure W) :
    (modificationCenterSheaf W s).comap (leftSmoothPointAddition W a b h) ≤
      (modificationCenterSheaf W s).comap b := by
  have he := comap_mono (pullback.lift a b h)
    (leftSmoothFactorAddition_center_le W s b3 b4 b6 h3 h4 h6)
  simpa only [← comap_comp, pullback.lift_snd, leftSmoothPointAddition] using he

end FLT.Mazur.WeierstrassIntegralChart
