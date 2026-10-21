/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothCoefficientAddition
public import FLT.Mazur.WeierstrassCoefficientMonoidalComparison
public import FLT.Mazur.WeierstrassSmoothCoefficientGroupIso
public import FLT.Mazur.WeierstrassSmoothWholeAction

/-!
# Equivariance of the whole-cubic coefficient isomorphism

The actual smooth-group and whole-curve coefficient isomorphisms identify
the original full action with its categorical pullback. No discriminant
unit assumption is used, so this comparison includes singular fibers.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)
local notation "V" => W.map (algebraMap R S)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "F" => Over.pullback q

/-- The monoidal comparison retains the actual smooth-by-whole coefficient map. -/
@[reassoc] theorem originalSmoothWholeCoefficientIso_product :
    (((originalSmoothCoefficientOverIso S W).hom ⊗ₘ
      (integralCurveCoefficientOverIso (S := S) W).hom) ≫
        Functor.LaxMonoidal.μ F _ _).left ≫
          pullback.fst ((integralSmoothGroup W).X ⊗ integralCurveOver W).hom q =
      originalLeftSmoothCoefficientProduct S W := by
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc]
    rw [Over.μ_pullback_left_fst_fst]
    erw [Over.tensorHom_left_fst_assoc]
    change _ ≫ (originalSmoothCoefficientIso S W).hom ≫ _ = _
    erw [originalSmoothCoefficientIso_fst]
    exact (originalLeftSmoothCoefficientProduct_fst S W).symm
  · simp only [Over.comp_left, Category.assoc]
    rw [Over.μ_pullback_left_fst_snd]
    erw [Over.tensorHom_left_snd_assoc]
    rw [integralCurveCoefficientOverIso_fst]
    exact (originalLeftSmoothCoefficientProduct_snd S W).symm

/-- The entire original action is carried to the categorical coefficient pullback action. -/
theorem originalSmoothWholeCoefficientIso_action :
    integralSmoothWholeAction V ≫ (integralCurveCoefficientOverIso (S := S) W).hom =
      ((originalSmoothCoefficientOverIso S W).hom ⊗ₘ
        (integralCurveCoefficientOverIso (S := S) W).hom) ≫
          Functor.LaxMonoidal.μ F _ _ ≫ (F).map (integralSmoothWholeAction W) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc]
    rw [integralCurveCoefficientOverIso_fst]
    change leftSmoothFactorAddition V ≫ integralCoefficientMorphism W =
      _ ≫ _ ≫ pullback.lift _ _ _ ≫ _
    rw [pullback.lift_fst]
    change _ = _ ≫ _ ≫ _ ≫ leftSmoothFactorAddition W
    have hp := congrArg (fun k => k ≫ leftSmoothFactorAddition W)
      (originalSmoothWholeCoefficientIso_product S W)
    exact (originalLeftSmoothCoefficientMap_addition S W).trans
      (by simpa only [Over.comp_left, Category.assoc] using hp.symm)
  · exact (Over.w _).trans (Over.w _).symm

end FLT.Mazur.WeierstrassDividedDepth
