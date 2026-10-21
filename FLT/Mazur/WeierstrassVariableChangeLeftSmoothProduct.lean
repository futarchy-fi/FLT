/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassVariableChangeIntrinsicGroup
public import FLT.Mazur.WeierstrassLeftSmoothCoefficientAddition
public import FLT.Mazur.WeierstrassSmoothWholeAction

/-!
# Admissible changes on smooth-by-whole input products

The actual product comparison retains the smooth first input and the entire
second cubic, together with their original proper product inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassDividedDepth
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (C : VariableChange R) (h : C • W = V)
local notation "e" => integralVariableChangeSmoothMap W V C h
local notation "E" => integralVariableChangeIso W V C h

/-- The actual coordinate change on a smooth first input and arbitrary second input. -/
irreducible_def integralVariableChangeLeftSmoothProduct :
    leftSmoothFactorProduct V ⟶ leftSmoothFactorProduct W :=
  pullback.lift (pullback.fst _ _ ≫ e) (pullback.snd _ _ ≫ (E).hom) (by
    rw [Category.assoc, Category.assoc, integralVariableChangeSmoothMap_structure]
    change _ = _ ≫ integralVariableChangeTo W V C h ≫ integralCurveStructure W
    rw [integralVariableChangeTo_structure]
    exact pullback.condition)

/-- The first projection is exactly the original smooth comparison. -/
@[reassoc] theorem integralVariableChangeLeftSmoothProduct_fst :
    integralVariableChangeLeftSmoothProduct W V C h ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ e := by
  rw [integralVariableChangeLeftSmoothProduct_def]
  exact pullback.lift_fst _ _ _

/-- The second projection retains the whole original cubic comparison. -/
@[reassoc] theorem integralVariableChangeLeftSmoothProduct_snd :
    integralVariableChangeLeftSmoothProduct W V C h ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ (E).hom := by
  rw [integralVariableChangeLeftSmoothProduct_def]
  exact pullback.lift_snd _ _ _

/-- The enlarged input comparison retains the original proper product map. -/
@[reassoc] theorem integralVariableChangeLeftSmoothProduct_inclusion :
    integralVariableChangeLeftSmoothProduct W V C h ≫ leftSmoothFactorsInclusion W =
      leftSmoothFactorsInclusion V ≫ integralVariableChangeProduct W V C h := by
  apply pullback.hom_ext
  · simp only [Category.assoc, leftSmoothFactorsInclusion_fst,
      integralVariableChangeLeftSmoothProduct_fst_assoc,
      integralVariableChangeSmoothMap_inclusion, integralVariableChangeProduct_fst,
      leftSmoothFactorsInclusion_fst_assoc]
  · simp only [Category.assoc, leftSmoothFactorsInclusion_snd,
      integralVariableChangeLeftSmoothProduct_snd, integralVariableChangeProduct_snd,
      leftSmoothFactorsInclusion_snd_assoc]

/-- The tensor of the original comparisons is the actual enlarged input comparison. -/
theorem integralVariableChangeLeftSmoothProduct_tensor :
    ((integralVariableChangeSmoothOverIso W V C h).hom ⊗ₘ
      (integralVariableChangeOverIso W V C h).hom).left =
        integralVariableChangeLeftSmoothProduct W V C h := by
  apply pullback.hom_ext
  · exact (Over.tensorHom_left_fst _ _ _ _).trans
      (integralVariableChangeLeftSmoothProduct_fst W V C h).symm
  · exact (Over.tensorHom_left_snd _ _ _ _).trans
      (integralVariableChangeLeftSmoothProduct_snd W V C h).symm

end FLT.Mazur.WeierstrassIntegralChart
