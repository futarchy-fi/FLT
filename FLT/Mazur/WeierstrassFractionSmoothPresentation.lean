/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModifiedSmoothOutputCoordinates
public import FLT.Mazur.WeierstrassLeftSmoothFractionActionGluing

/-!
# Actual affine presentations over original fraction inputs

The smooth product of every original fraction chart has a complete affine
output refinement. Its original second-input coordinates factor through
the flat projection, and its output coordinates present the actual action.
These are constructed presentations, with no arbitrary test-ring flatness.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s : R)
  (f : Coordinate W 2)

/-- The original fraction input contracts to the original affine cubic chart. -/
def fractionSmoothContraction :
    Spec (.of (BlowupFractionChart.chart (modificationChartCenter W s 2) f)) ⟶
      integralCurve W :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (Coordinate W 2) (BlowupFractionChart.chart (modificationChartCenter W s 2) f))) ≫
      integralCurveChart W 2

/-- The actual complete affine refinement of the smooth product of this fraction chart. -/
abbrev fractionSmoothCover := modifiedSmoothAffineCover W (fractionSmoothContraction W s f)

/-- The original second input on every actual affine member. -/
def fractionSmoothOriginalHom (i : (fractionSmoothCover W s f).I₀) :
    Coordinate W 2 →+* (fractionSmoothCover W s f).X i :=
  (modifiedSmoothAffineInputHom W (fractionSmoothContraction W s f) i).comp
    (algebraMap (Coordinate W 2) (BlowupFractionChart.chart (modificationChartCenter W s 2) f))

/-- Original second-input coordinates give the exact contracted input. -/
@[reassoc] theorem fractionSmoothOriginalHom_spec (i : (fractionSmoothCover W s f).I₀) :
    Spec.map (CommRingCat.ofHom (fractionSmoothOriginalHom W s f i)) ≫ integralCurveChart W 2 =
      modifiedSmoothAffineProjection W (fractionSmoothContraction W s f) i ≫
        fractionSmoothContraction W s f := by
  unfold fractionSmoothOriginalHom fractionSmoothContraction
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    modifiedSmoothAffineInputHom_spec]

/-- The actual original pair on every refined fraction input agrees over the base. -/
theorem fractionSmoothParameter_structure (i : (fractionSmoothCover W s f).I₀) :
    modifiedSmoothAffineParameter W (fractionSmoothContraction W s f) i ≫
        integralSmoothStructure W =
      (Spec.map (CommRingCat.ofHom (fractionSmoothOriginalHom W s f i)) ≫
        integralCurveChart W 2) ≫ integralCurveStructure W := by
  rw [fractionSmoothOriginalHom_spec]
  exact modifiedSmoothAffineParameter_structure W (fractionSmoothContraction W s f) i

/-- Output members assigned to the affine cubic chart present the actual original addition. -/
theorem fractionSmoothOutput_addition (i : (fractionSmoothCover W s f).I₀)
    (hi : modifiedSmoothOutputIndex W (fractionSmoothContraction W s f) i = 2) :
    Spec.map (CommRingCat.ofHom
        (modifiedSmoothOutputHomAt W (fractionSmoothContraction W s f) i 2 hi)) ≫
          integralCurveChart W 2 =
      leftSmoothPointAddition W
        (modifiedSmoothAffineParameter W (fractionSmoothContraction W s f) i)
        (Spec.map (CommRingCat.ofHom (fractionSmoothOriginalHom W s f i)) ≫
          integralCurveChart W 2) (fractionSmoothParameter_structure W s f i) := by
  simpa only [fractionSmoothOriginalHom_spec] using
    modifiedSmoothOutputHomAt_addition W (fractionSmoothContraction W s f) i 2 hi

/-- The original denominator is regular on every member of this actual cover. -/
theorem fractionSmoothOriginalHom_regular (i : (fractionSmoothCover W s f).I₀) :
    IsRegular (fractionSmoothOriginalHom W s f i f) := by
  exact flatRingHom_isRegular
    (modifiedSmoothAffineInputHom W (fractionSmoothContraction W s f) i)
    (modifiedSmoothAffineInputHom_flat W (fractionSmoothContraction W s f) i)
    (BlowupFractionChart.denominator_regular (modificationChartCenter W s 2) f)

end FLT.Mazur.WeierstrassIntegralChart
