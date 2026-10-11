/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothPointAssociativity
public import FLT.Mazur.WeierstrassLeftSmoothIdentity
public import FLT.Mazur.WeierstrassSmoothAdditionInverse

/-!
# Inverse translations on the whole original cubic

The actual smooth negation undoes translation on arbitrary scheme-valued points,
including points supported on the singular locus of a bad fiber.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The actual smooth sum with the negative first input is the actual zero section. -/
theorem smoothPairPointAddition_left_neg {X : Scheme.{u}}
    (a : X ⟶ (integralSmoothOpen W).toScheme)
    (h : (a ≫ integralSmoothNegation W) ≫ integralSmoothStructure W =
      a ≫ integralSmoothStructure W) :
    smoothPairPointAddition W (a ≫ integralSmoothNegation W) a h =
      a ≫ integralSmoothStructure W ≫ integralSmoothZero W := by
  have hp : pullback.lift (a ≫ integralSmoothNegation W) a h =
      a ≫ smoothFactorLeftNegation W := by
    apply pullback.hom_ext <;>
      simp only [smoothFactorLeftNegation, Category.assoc,
        pullback.lift_fst, pullback.lift_snd, Category.comp_id]
  rw [smoothPairPointAddition, hp, Category.assoc, smoothFactorAddition_left_inverse]

/-- Translating by the actual negative undoes the original action on the whole cubic. -/
theorem leftSmoothPointAddition_neg_cancel {X : Scheme.{u}}
    (a : X ⟶ (integralSmoothOpen W).toScheme) (b : X ⟶ integralCurve W)
    (hab : a ≫ integralSmoothStructure W = b ≫ integralCurveStructure W) :
    leftSmoothPointAddition W (a ≫ integralSmoothNegation W)
      (leftSmoothPointAddition W a b hab)
      (by rw [Category.assoc, integralSmoothNegation_structure,
        leftSmoothPointAddition_structure]) = b := by
  have he := leftSmoothPointAddition_assoc W (a ≫ integralSmoothNegation W) a b
    (by rw [Category.assoc, integralSmoothNegation_structure]) hab
  have hz : a ≫ integralSmoothStructure W ≫ integralSmoothZero W =
      b ≫ integralCurveStructure W ≫ integralSmoothZero W := by
    rw [← Category.assoc, hab, Category.assoc]
  simpa only [smoothPairPointAddition_left_neg, hz, leftSmoothPointAddition_zero] using he.symm

/-- Translation also undoes the action by its actual negative. -/
theorem leftSmoothPointAddition_cancel_neg {X : Scheme.{u}}
    (a : X ⟶ (integralSmoothOpen W).toScheme) (b : X ⟶ integralCurve W)
    (hab : a ≫ integralSmoothStructure W = b ≫ integralCurveStructure W) :
    leftSmoothPointAddition W a
      (leftSmoothPointAddition W (a ≫ integralSmoothNegation W) b
        (by rw [Category.assoc, integralSmoothNegation_structure]; exact hab))
      (by rw [leftSmoothPointAddition_structure, Category.assoc,
        integralSmoothNegation_structure]) = b := by
  have he := leftSmoothPointAddition_neg_cancel W (a ≫ integralSmoothNegation W) b
    (by rw [Category.assoc, integralSmoothNegation_structure]; exact hab)
  simpa only [Category.assoc, integralSmoothNegation_comp, Category.comp_id] using he

/-- Enlarged point addition commutes with changing the scheme of points. -/
theorem leftSmoothPointAddition_comp {X Y : Scheme.{u}} (f : Y ⟶ X)
    (a : X ⟶ (integralSmoothOpen W).toScheme) (b : X ⟶ integralCurve W)
    (h : a ≫ integralSmoothStructure W = b ≫ integralCurveStructure W) :
    leftSmoothPointAddition W (f ≫ a) (f ≫ b)
      (by simp only [Category.assoc, h]) = f ≫ leftSmoothPointAddition W a b h := by
  have hp : pullback.lift (f ≫ a) (f ≫ b) (by simp only [Category.assoc, h]) =
      f ≫ pullback.lift a b h := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]
  rw [leftSmoothPointAddition, hp, Category.assoc]
  rfl

end FLT.Mazur.WeierstrassIntegralChart
