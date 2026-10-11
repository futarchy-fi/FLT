/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothAffineCenter
public import FLT.Mazur.WeierstrassLeftSmoothInputAddition

/-!
# Center containment on the original simultaneous affine overlaps

Transporting the proved affine containment keeps the original global second
input. No replacement of the center by its reduced support is involved.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.IdealSheafData
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4)

include h3 h4

/-- Affine containment retains the second projection of the actual integral input product. -/
theorem leftSmoothAffineAddition_center_le_global :
    (modificationCenterSheaf W s).comap (leftSmoothAffineAddition W) ≤
      (modificationCenterSheaf W s).comap
        ((leftSmoothAffineInputOpen W).ι ≫ integralCurveProductChart W false false ≫
          pullback.snd (integralCurveStructure W) (integralCurveStructure W)) := by
  rw [integralCurveProductChart_snd]
  exact leftSmoothAffineAddition_center_le W s b3 b4 h3 h4

/-- Simultaneous input normalization preserves full center containment. -/
theorem leftSmoothAffineOverlapAddition_center_le (b c : Bool) :
    (modificationCenterSheaf W s).comap (leftSmoothAffineOverlapAddition W b c) ≤
      (modificationCenterSheaf W s).comap
        (leftSmoothAffineOverlapInput W b c ≫ integralCurveProductChart W b c ≫
          pullback.snd (integralCurveStructure W) (integralCurveStructure W)) := by
  have h := comap_mono (leftSmoothAffineOverlapToInputs W b c)
    (leftSmoothAffineAddition_center_le_global W s b3 b4 h3 h4)
  simpa only [← comap_comp, Category.assoc,
    leftSmoothAffineOverlapToInputs_global_assoc, leftSmoothAffineOverlapAddition] using h

end FLT.Mazur.WeierstrassIntegralChart
