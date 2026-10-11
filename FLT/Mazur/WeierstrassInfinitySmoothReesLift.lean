/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothChartCenterEquality
public import FLT.Mazur.WeierstrassModifiedSmoothOutputCoordinates
public import FLT.Mazur.WeierstrassLeftSmoothFractionActionGluing

/-!
# Lifting the actual infinity-input action on affine output domains

The entire original Y input has unit center. Center invariance therefore
principalizes the output center by 1 on every affine-output member of its
actual smooth-product cover. This supplies a genuine Rees lift without an
input fraction-chart presentation or an arbitrary flatness assumption.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s * b6)
  (i : (modifiedSmoothAffineCover W (integralCurveChart W 1)).I₀)
  (hi : modifiedSmoothOutputIndex W (integralCurveChart W 1) i = 2)

include h3 h4 h6 in
/-- The actual affine output center is the unit ideal on every original infinity-input member. -/
theorem infinitySmoothOutput_center :
    (modificationChartCenter W s 2).map
      (modifiedSmoothOutputHomAt W (integralCurveChart W 1) i 2 hi) = ⊤ := by
  have hp : modifiedSmoothAffineParameter W (integralCurveChart W 1) i ≫
      integralSmoothStructure W =
      (Spec.map (CommRingCat.ofHom
        (modifiedSmoothAffineInputHom W (integralCurveChart W 1) i)) ≫
          integralCurveChart W 1) ≫ integralCurveStructure W :=
    (modifiedSmoothAffineParameter_structure W (integralCurveChart W 1) i).trans
      (congrArg (fun g => (g ≫ integralCurveChart W 1) ≫ integralCurveStructure W)
        (modifiedSmoothAffineInputHom_spec W (integralCurveChart W 1) i).symm)
  apply leftSmoothChartPresentation_center_eq_top W s b3 b4 b6 h3 h4 h6 1 2 (Or.inr rfl)
    (modifiedSmoothAffineParameter W (integralCurveChart W 1) i)
    (modifiedSmoothOutputHomAt W (integralCurveChart W 1) i 2 hi)
    (modifiedSmoothAffineInputHom W (integralCurveChart W 1) i) hp
  simpa only [modifiedSmoothAffineInputHom_spec] using
    modifiedSmoothOutputHomAt_addition W (integralCurveChart W 1) i 2 hi

/-- Lift the actual infinity-input action on this entire affine output presentation. -/
irreducible_def infinitySmoothPresentationToRees :
    Spec ((modifiedSmoothAffineCover W (integralCurveChart W 1)).X i) ⟶
      BlowupRees.proj (modificationChartCenter W s 2) :=
  RegularCenter.gluedLift (modificationChartCenter W s 2)
    (modifiedSmoothOutputHomAt W (integralCurveChart W 1) i 2 hi) 1
    ((infinitySmoothOutput_center W s b3 b4 b6 h3 h4 h6 i hi).trans
      Ideal.span_singleton_one.symm) isRegular_one
    (WeierstrassModificationReesCoordinates.centerGenerators W s)
    (WeierstrassModificationReesCoordinates.centerGenerators_mem W s)
    (WeierstrassModificationReesCoordinates.centerGenerators_span W s)

/-- The infinity-input lift preserves the exact original output coordinates. -/
@[reassoc] theorem infinitySmoothPresentationToRees_contraction :
    infinitySmoothPresentationToRees W s b3 b4 b6 h3 h4 h6 i hi ≫
        BlowupRees.contraction (modificationChartCenter W s 2) =
      Spec.map (CommRingCat.ofHom
        (modifiedSmoothOutputHomAt W (integralCurveChart W 1) i 2 hi)) := by
  rw [infinitySmoothPresentationToRees_def, RegularCenter.gluedLift_contraction]

/-- The infinity-input lift contracts to exactly the actual restricted original action. -/
@[reassoc] theorem infinitySmoothPresentationToRees_action :
    infinitySmoothPresentationToRees W s b3 b4 b6 h3 h4 h6 i hi ≫
        BlowupRees.contraction (modificationChartCenter W s 2) ≫ integralCurveChart W 2 =
      (modifiedSmoothAffineCover W (integralCurveChart W 1)).f i ≫
        modifiedSmoothAffineAddition W (integralCurveChart W 1) := by
  rw [infinitySmoothPresentationToRees_contraction_assoc,
    modifiedSmoothOutputHomAt_addition, ← modifiedSmoothAffineCover_addition]

end FLT.Mazur.WeierstrassIntegralChart
