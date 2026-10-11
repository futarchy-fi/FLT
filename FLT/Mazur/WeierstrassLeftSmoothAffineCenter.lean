/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAdditionCenterSheaf
public import FLT.Mazur.WeierstrassLeftSmoothAffineAddition
public import FLT.Mazur.IdealSheafOpenCoverDetection

/-!
# Center preservation on the complete left smooth affine input open

The full scheme-theoretic center containment descends from the four original
addition charts. Singular second inputs and nonreduced coefficients are retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open Scheme.IdealSheafData
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4)

include h3 h4 in
/-- The actual descended affine-input law preserves the full center ideal. -/
theorem leftSmoothAffineAddition_center_le :
    (modificationCenterSheaf W s).comap (leftSmoothAffineAddition W) ≤
      (modificationCenterSheaf W s).comap
        ((leftSmoothAffineInputOpen W).ι ≫
          Spec.map (CommRingCat.ofHom (productRight W).toRingHom) ≫ integralCurveChart W 2) := by
  apply BaseAdicThickening.idealSheaf_le_of_openCover (leftSmoothAffineAdditionCover W)
  intro i
  have h := comap_mono (leftSmoothAffineAdditionProjection W i)
    (additionCurveChart_center_le W s b3 b4 h3 h4 i)
  simpa only [← comap_comp, leftSmoothAffineAdditionProjection_addition,
    ← Category.assoc, leftSmoothAffineAdditionProjection_inputs] using h

end FLT.Mazur.WeierstrassIntegralChart
