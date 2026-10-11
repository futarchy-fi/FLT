/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothGlobalCenter
public import FLT.Mazur.WeierstrassLeftSmoothInverseAction

/-!
# Scheme-theoretic invariance of the modification center

Apply the proved forward containment to the actual negative smooth translation.
The original inverse action identity supplies reverse containment. Thus the
full ideals agree over every scheme of points, including nonreduced ones.
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

/-- Actual inverse translation upgrades containment to equality of full center ideals. -/
theorem leftSmoothPointAddition_center_eq {X : Scheme.{u}}
    (a : X ⟶ (integralSmoothOpen W).toScheme) (b : X ⟶ integralCurve W)
    (h : a ≫ integralSmoothStructure W = b ≫ integralCurveStructure W) :
    (modificationCenterSheaf W s).comap (leftSmoothPointAddition W a b h) =
      (modificationCenterSheaf W s).comap b := by
  apply le_antisymm (leftSmoothPointAddition_center_le W s b3 b4 b6 h3 h4 h6 a b h)
  have he := leftSmoothPointAddition_center_le W s b3 b4 b6 h3 h4 h6
    (a ≫ integralSmoothNegation W) (leftSmoothPointAddition W a b h)
    (by rw [Category.assoc, integralSmoothNegation_structure,
      leftSmoothPointAddition_structure])
  simpa only [leftSmoothPointAddition_neg_cancel] using he

/-- The actual action and the original second projection pull back exactly the same center. -/
theorem leftSmoothFactorAddition_center_eq :
    (modificationCenterSheaf W s).comap (leftSmoothFactorAddition W) =
      (modificationCenterSheaf W s).comap
        (pullback.snd (integralSmoothStructure W) (integralCurveStructure W)) := by
  have h := leftSmoothPointAddition_center_eq W s b3 b4 b6 h3 h4 h6
    (pullback.fst (integralSmoothStructure W) (integralCurveStructure W))
    (pullback.snd (integralSmoothStructure W) (integralCurveStructure W)) pullback.condition
  have hi : pullback.lift
      (pullback.fst (integralSmoothStructure W) (integralCurveStructure W))
      (pullback.snd (integralSmoothStructure W) (integralCurveStructure W))
      pullback.condition = 𝟙 _ := by
    apply pullback.hom_ext <;> simp only [pullback.lift_fst, pullback.lift_snd, Category.id_comp]
  simpa only [leftSmoothPointAddition, hi, Category.id_comp] using h

/-- Every power of the full center is also preserved, for later Rees constructions. -/
theorem leftSmoothFactorAddition_center_pow (n : ℕ) :
    (modificationCenterSheaf W s ^ n).comap (leftSmoothFactorAddition W) =
      (modificationCenterSheaf W s ^ n).comap
        (pullback.snd (integralSmoothStructure W) (integralCurveStructure W)) := by
  rw [FCurve.idealSheaf_comap_pow, FCurve.idealSheaf_comap_pow,
    leftSmoothFactorAddition_center_eq W s b3 b4 b6 h3 h4 h6]

end FLT.Mazur.WeierstrassIntegralChart
