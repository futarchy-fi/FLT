/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothFactorAddition
public import FLT.Mazur.WeierstrassSmoothZeroSection

/-!
# The zero graph for the whole original cubic

The actual smooth zero section pairs with every point of the original cubic,
including singular points, and retains both original projective inputs.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Pair the smooth zero section with the identity of the whole cubic. -/
def leftSmoothFactorZero : integralCurve W ⟶ leftSmoothFactorProduct W :=
  pullback.lift (integralCurveStructure W ≫ integralSmoothZero W) (𝟙 _)
    (by rw [Category.assoc, integralSmoothZero_structure, Category.comp_id, Category.id_comp])

/-- The first factor is the actual smooth zero section. -/
@[reassoc] theorem leftSmoothFactorZero_fst :
    leftSmoothFactorZero W ≫ pullback.fst _ _ =
      integralCurveStructure W ≫ integralSmoothZero W := pullback.lift_fst _ _ _

/-- The second factor retains every original point. -/
@[reassoc] theorem leftSmoothFactorZero_snd :
    leftSmoothFactorZero W ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _

/-- Inclusion gives exactly the original global left-zero graph. -/
@[reassoc] theorem leftSmoothFactorZero_inclusion :
    leftSmoothFactorZero W ≫ leftSmoothFactorsInclusion W = integralCurveLeftZero W := by
  apply pullback.hom_ext
  · rw [Category.assoc, leftSmoothFactorsInclusion, pullback.lift_fst,
      leftSmoothFactorZero_fst_assoc, integralSmoothZero_inclusion,
      integralCurveLeftZero_fst]
  · rw [Category.assoc, leftSmoothFactorsInclusion, pullback.lift_snd,
      leftSmoothFactorZero_snd, integralCurveLeftZero_snd]

/-- The whole original cubic maps to the left smooth input open along its zero graph. -/
def leftSmoothProductZero : integralCurve W ⟶ (leftSmoothCurveProductOpen W).toScheme :=
  leftSmoothFactorZero W ≫ leftSmoothFactorsToProduct W

/-- Transport to the input open preserves the original projective pair. -/
@[reassoc] theorem leftSmoothProductZero_inclusion :
    leftSmoothProductZero W ≫ (leftSmoothCurveProductOpen W).ι = integralCurveLeftZero W := by
  rw [leftSmoothProductZero, Category.assoc, leftSmoothFactorsToProduct_inclusion,
    leftSmoothFactorZero_inclusion]

end FLT.Mazur.WeierstrassIntegralChart
