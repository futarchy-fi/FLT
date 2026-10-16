/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentitySmoothActionRotation

/-!
# Rotation of the entire original action input

Only the second factor rotates. The construction includes singular inputs
and preserves the original first parameter and power-series coefficient map.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open GroupObjectPointTranslation
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeRotation
attribute [local instance] exactVeroneseProjToBase_lfp completeSmoothGrpObj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "G" => completePointOriginalBaseGroup K n h (0 : Fin n)
local notation "M" => completeOriginalSmoothOver K n h
local notation "π" => exactVeroneseProjToBase K n h
local notation "P" => completeIdentityActionProduct K n h 0
local notation "r" => pullback.fst
  (Over.hom (CommGrp.X (G))) (π)
local notation "s" => pullback.snd
  (Over.hom (CommGrp.X (G))) (π)

/-- Rotate the original whole second input, including all singular points. -/
def completeIdentityActionInputRotation (b : ZMod n) : (P) ⟶ (P) :=
  pullback.lift (r) ((s) ≫ completeRotation K n h b) (by
    rw [Category.assoc, completeRotation_toBase]
    exact pullback.condition)

/-- The original identity parameter is unchanged. -/
@[reassoc] theorem completeIdentityActionInputRotation_fst (b : ZMod n) :
    completeIdentityActionInputRotation K n h b ≫ (r) = (r) := pullback.lift_fst _ _ _

/-- The original second input is rotated without any restriction of its domain. -/
@[reassoc] theorem completeIdentityActionInputRotation_snd (b : ZMod n) :
    completeIdentityActionInputRotation K n h b ≫ (s) =
      (s) ≫ completeRotation K n h b := pullback.lift_snd _ _ _

/-- Rotation preserves the original coefficient morphism. -/
@[reassoc] theorem completeIdentityActionInputRotation_structure (b : ZMod n) :
    completeIdentityActionInputRotation K n h b ≫ (s) ≫ (π) = (s) ≫ (π) := by
  rw [completeIdentityActionInputRotation_snd_assoc, completeRotation_toBase]

/-- These whole-input morphisms retain the exact cyclic composition law. -/
theorem completeIdentityActionInputRotation_add (b c : ZMod n) :
    completeIdentityActionInputRotation K n h (b + c) =
      completeIdentityActionInputRotation K n h b ≫
        completeIdentityActionInputRotation K n h c := by
  apply pullback.hom_ext
  · simp only [Category.assoc, completeIdentityActionInputRotation_fst]
  · simp only [Category.assoc, completeIdentityActionInputRotation_snd,
      completeIdentityActionInputRotation_snd_assoc, completeRotation_add]

/-- On smooth inputs the whole-input rotation is the actual cyclic translation. -/
@[reassoc] theorem completeIdentitySmoothActionInput_rotation (b : ZMod n) :
    (𝟙 (G).X ⊗ₘ translation (completeOriginalSmoothCyclicPoint K n h b)).left ≫
      completeIdentitySmoothActionInput K n h =
        completeIdentitySmoothActionInput K n h ≫
          completeIdentityActionInputRotation K n h b := by
  apply pullback.hom_ext
  · simp only [Category.assoc, completeIdentitySmoothActionInput_fst,
      completeIdentityActionInputRotation_fst]
    have he := congrArg Over.Hom.left
      (tensorHom_fst (𝟙 (G).X) (translation (completeOriginalSmoothCyclicPoint K n h b)))
    change _ ≫ pullback.fst (G).X.hom (M).hom =
      pullback.fst (G).X.hom (M).hom ≫ 𝟙 _ at he
    simpa only [Category.comp_id] using he
  · simp only [Category.assoc, completeIdentitySmoothActionInput_snd,
      completeIdentityActionInputRotation_snd]
    have he := congrArg Over.Hom.left
      (tensorHom_snd (𝟙 (G).X) (translation (completeOriginalSmoothCyclicPoint K n h b)))
    change _ ≫ pullback.snd (G).X.hom (M).hom =
      pullback.snd (G).X.hom (M).hom ≫ _ at he
    rw [← Category.assoc, he, Category.assoc,
      completeOriginalSmooth_translation_rotation, completeIdentitySmoothActionInput_snd_assoc]

end FLT.Mazur.PolygonInfinitesimalStages
