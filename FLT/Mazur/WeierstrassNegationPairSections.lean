/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalNegationInvolution

/-!
# Actual point-negation sections of the cubic product

Pairing a point with its constructed negation gives genuine sections into the
fiber product over the coefficient spectrum. Their affine restriction is an
explicit tensor evaluation, on which both ordinary slope denominators vanish.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The product section pairing the original point with its negation. -/
def integralCurveRightNegation : integralCurve W ⟶ integralCurveProduct W :=
  pullback.lift (𝟙 _) (integralCurveNegation W)
    (by rw [Category.id_comp, integralCurveNegation_structure])

/-- Its first projection is the original point. -/
theorem integralCurveRightNegation_fst :
    integralCurveRightNegation W ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst ..

/-- Its second projection is the constructed global negation. -/
theorem integralCurveRightNegation_snd :
    integralCurveRightNegation W ≫ pullback.snd _ _ = integralCurveNegation W :=
  pullback.lift_snd ..

/-- The opposite product section pairs the negation with the original point. -/
def integralCurveLeftNegation : integralCurve W ⟶ integralCurveProduct W :=
  pullback.lift (integralCurveNegation W) (𝟙 _)
    (by rw [Category.id_comp, integralCurveNegation_structure])

/-- The first projection of the opposite section is negation. -/
theorem integralCurveLeftNegation_fst :
    integralCurveLeftNegation W ≫ pullback.fst _ _ = integralCurveNegation W :=
  pullback.lift_fst ..

/-- The second projection of the opposite section is the original point. -/
theorem integralCurveLeftNegation_snd :
    integralCurveLeftNegation W ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd ..

/-- Negating the input interchanges the two actual product sections. -/
theorem integralCurveNegation_rightNegation :
    integralCurveNegation W ≫ integralCurveRightNegation W = integralCurveLeftNegation W := by
  apply pullback.hom_ext
  · rw [Category.assoc, integralCurveRightNegation_fst, Category.comp_id,
      integralCurveLeftNegation_fst]
  · rw [Category.assoc, integralCurveRightNegation_snd, integralCurveNegation_comp,
      integralCurveLeftNegation_snd]

/-- The explicit tensor evaluation at an affine point and its negation. -/
def affineNegationPair : AffineProduct W →ₐ[R] Coordinate W 2 :=
  Algebra.TensorProduct.lift (AlgHom.id R _) (affineNegation W) (fun _ _ => Commute.all ..)

/-- The first affine input remains the universal point. -/
theorem affineNegationPair_left :
    (affineNegationPair W).comp (productLeft W) = AlgHom.id R (Coordinate W 2) :=
  Algebra.TensorProduct.lift_comp_includeLeft _ _ _

/-- The second affine input is exactly the integral negation. -/
theorem affineNegationPair_right :
    (affineNegationPair W).comp (productRight W) = affineNegation W :=
  Algebra.TensorProduct.lift_comp_includeRight' _ _ _

/-- The first X coordinate evaluates to the original X. -/
@[simp] theorem affineNegationPair_x₁ : affineNegationPair W (productX₁ W) = coord W 2 0 :=
  DFunLike.congr_fun (affineNegationPair_left W) (coord W 2 0)

/-- The first Y coordinate evaluates to the original Y. -/
@[simp] theorem affineNegationPair_y₁ : affineNegationPair W (productY₁ W) = coord W 2 1 :=
  DFunLike.congr_fun (affineNegationPair_left W) (coord W 2 1)

/-- The negated point has the same X coordinate. -/
@[simp] theorem affineNegationPair_x₂ : affineNegationPair W (productX₂ W) = coord W 2 0 :=
  (DFunLike.congr_fun (affineNegationPair_right W) (coord W 2 0)).trans (affineNegation_x W)

/-- The second Y coordinate is the affine negation formula. -/
@[simp] theorem affineNegationPair_y₂ :
    affineNegationPair W (productY₂ W) = -coord W 2 1 -
      algebraMap R _ W.a₁ * coord W 2 0 - algebraMap R _ W.a₃ :=
  (DFunLike.congr_fun (affineNegationPair_right W) (coord W 2 1)).trans (affineNegation_y W)

/-- The affine point-negation pair lies on the vanishing ordinary secant denominator. -/
theorem affineNegationPair_secantDenominator :
    affineNegationPair W (secantDenominator W) = 0 := by
  rw [map_secantDenominator, affineNegationPair_x₁, affineNegationPair_x₂, sub_self]

/-- The ordinary tangent denominator also vanishes on the entire point-negation pair. -/
theorem affineNegationPair_tangentDenominator :
    affineNegationPair W (tangentDenominator W) = 0 := by
  rw [map_tangentDenominator, affineNegationPair_y₁, affineNegationPair_y₂,
    affineNegationPair_x₂]
  ring

/-- The actual global right-negation section restricts to the explicit affine tensor map. -/
theorem integralCurveChart_rightNegation_affine :
    integralCurveChart W 2 ≫ integralCurveRightNegation W =
      Spec.map (CommRingCat.ofHom (affineNegationPair W).toRingHom) ≫
        integralCurveProductChart W false false := by
  apply pullback.hom_ext
  · rw [Category.assoc, integralCurveRightNegation_fst, Category.comp_id,
      Category.assoc, integralCurveProductChart_fst, ← Category.assoc, ← Spec.map_comp]
    change integralCurveChart W 2 = Spec.map (CommRingCat.ofHom
      ((affineNegationPair W).comp (productLeft W)).toRingHom) ≫ integralCurveChart W 2
    rw [affineNegationPair_left]
    simp
  · rw [Category.assoc, integralCurveRightNegation_snd, integralCurveChart_negation_affine,
      Category.assoc, integralCurveProductChart_snd, ← Category.assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (affineNegation W).toRingHom) ≫ integralCurveChart W 2 =
      Spec.map (CommRingCat.ofHom
        ((affineNegationPair W).comp (productRight W)).toRingHom) ≫ integralCurveChart W 2
    rw [affineNegationPair_right]

end FLT.Mazur.WeierstrassIntegralChart
