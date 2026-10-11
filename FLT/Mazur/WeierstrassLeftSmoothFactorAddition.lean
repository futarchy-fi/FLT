/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothAdditionStructure
public import FLT.Mazur.WeierstrassLeftSmoothFactorProduct

/-!
# Integral addition of a smooth point and an arbitrary point

Transporting the actual glued law gives a morphism from the smooth by whole
cubic fiber product into the original cubic, over the original coefficient scheme.
The group-action identities are separate assertions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Integral addition on the categorical product of the smooth and whole original curves. -/
def leftSmoothFactorAddition : leftSmoothFactorProduct W ⟶ integralCurve W :=
  leftSmoothFactorsToProduct W ≫ leftSmoothCurveAddition W

/-- The categorical enlarged addition retains its actual coefficient morphism. -/
theorem leftSmoothFactorAddition_structure :
    leftSmoothFactorAddition W ≫ integralCurveStructure W =
      pullback.fst (integralSmoothStructure W) (integralCurveStructure W) ≫
        integralSmoothStructure W := by
  rw [leftSmoothFactorAddition, Category.assoc, leftSmoothCurveAddition_structure,
    leftSmoothFactorsToProduct_inclusion_assoc, ← Category.assoc,
    leftSmoothFactorsInclusion, pullback.lift_fst, Category.assoc]

/-- Returning to the original input open recovers its glued law exactly. -/
@[reassoc] theorem leftSmoothProductToFactors_addition :
    leftSmoothProductToFactors W ≫ leftSmoothFactorAddition W = leftSmoothCurveAddition W := by
  rw [leftSmoothFactorAddition, ← Category.assoc]
  have hi : leftSmoothProductToFactors W ≫ leftSmoothFactorsToProduct W = 𝟙 _ :=
    (leftSmoothProductFactorsIso W).hom_inv_id
  rw [hi, Category.id_comp]

/-- A compatible scheme-valued pair produces its actual integral sum. -/
def leftSmoothPointAddition {X : Scheme.{u}}
    (a : X ⟶ (integralSmoothOpen W).toScheme) (b : X ⟶ integralCurve W)
    (h : a ≫ integralSmoothStructure W = b ≫ integralCurveStructure W) :
    X ⟶ integralCurve W := pullback.lift a b h ≫ leftSmoothFactorAddition W

/-- Scheme-valued addition preserves the specified coefficient morphism. -/
@[reassoc] theorem leftSmoothPointAddition_structure {X : Scheme.{u}}
    (a : X ⟶ (integralSmoothOpen W).toScheme) (b : X ⟶ integralCurve W)
    (h : a ≫ integralSmoothStructure W = b ≫ integralCurveStructure W) :
    leftSmoothPointAddition W a b h ≫ integralCurveStructure W = a ≫ integralSmoothStructure W := by
  rw [leftSmoothPointAddition, Category.assoc, leftSmoothFactorAddition_structure,
    pullback.lift_fst_assoc]

end FLT.Mazur.WeierstrassIntegralChart
