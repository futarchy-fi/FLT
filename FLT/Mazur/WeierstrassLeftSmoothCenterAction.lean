/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothCenterInvariant

/-!
# Restriction of the integral action to the full modification center

Equality of the proved pullback ideals constructs the center-valued action.
Its square with the actual whole-cubic action is Cartesian: it retains the
entire scheme-theoretic preimage, rather than just the singular point support.
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

/-- The center in the unchanged second factor of the actual action product. -/
def leftSmoothCenterInputIdeal : (leftSmoothFactorProduct W).IdealSheafData :=
  (modificationCenterSheaf W s).comap
    (pullback.snd (integralSmoothStructure W) (integralCurveStructure W))

/-- The original whole-cubic action restricts to the full center subscheme. -/
def leftSmoothCenterAction : (leftSmoothCenterInputIdeal W s).subscheme ⟶
    (modificationCenterSheaf W s).subscheme :=
  subschemeMap (leftSmoothCenterInputIdeal W s) (modificationCenterSheaf W s)
    (leftSmoothFactorAddition W) (le_map_iff_comap_le.mpr
      (leftSmoothFactorAddition_center_eq W s b3 b4 b6 h3 h4 h6).le)

/-- This restriction has exactly the original integral action as its ambient map. -/
@[reassoc] theorem leftSmoothCenterAction_inclusion :
    leftSmoothCenterAction W s b3 b4 b6 h3 h4 h6 ≫ (modificationCenterSheaf W s).subschemeι =
      (leftSmoothCenterInputIdeal W s).subschemeι ≫ leftSmoothFactorAddition W :=
  subschemeMap_subschemeι _ _ _ _

/-- The restriction is the entire scheme-theoretic inverse image of the center. -/
theorem leftSmoothCenterAction_isPullback :
    IsPullback (leftSmoothCenterInputIdeal W s).subschemeι
      (leftSmoothCenterAction W s b3 b4 b6 h3 h4 h6)
      (leftSmoothFactorAddition W) (modificationCenterSheaf W s).subschemeι := by
  apply isPullback_of_isClosedImmersion
  · exact (leftSmoothCenterAction_inclusion W s b3 b4 b6 h3 h4 h6).symm
  · rw [ker_subschemeι, ker_subschemeι, leftSmoothFactorAddition_center_eq W s b3 b4 b6 h3 h4 h6]
    rfl

/-- The actual restricted action retains the original coefficient morphism. -/
@[reassoc] theorem leftSmoothCenterAction_structure :
    leftSmoothCenterAction W s b3 b4 b6 h3 h4 h6 ≫
        (modificationCenterSheaf W s).subschemeι ≫ integralCurveStructure W =
      (leftSmoothCenterInputIdeal W s).subschemeι ≫
        pullback.snd (integralSmoothStructure W) (integralCurveStructure W) ≫
          integralCurveStructure W := by
  rw [leftSmoothCenterAction_inclusion_assoc, leftSmoothFactorAddition_structure,
    pullback.condition]

end FLT.Mazur.WeierstrassIntegralChart
