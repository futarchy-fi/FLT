/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothGroupRotations
public import FLT.Mazur.PolygonCompleteIdentityActionMultiplication

/-!
# The identity chart acts on the entire original smooth polygon

Restrict the first input of the constructed full smooth multiplication.
Its input map retains the whole smooth second input in the original family.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeRotation
attribute [local instance] exactVeroneseProjToBase_lfp
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "G" => completePointOriginalBaseGroup K n h (0 : Fin n)
local notation "M" => completeOriginalSmoothOver K n h
local notation "π" => exactVeroneseProjToBase K n h
local notation "U" => completePointIdentityOpen K n h (0 : Fin n)
local notation "j" => completeIdentityChart K n h (0 : Fin n) 0

/-- The original zero chart is the unchanged identity-open inclusion. -/
@[reassoc] theorem completeIdentityChart_zero_inclusion :
    (j).left ≫ (π).smoothLocus.ι = (U).ι := by
  rw [completeIdentityChart_inclusion, completeRotation_zero, Category.comp_id]

/-- The identity group acts on the entire constructed smooth group by multiplication. -/
def completeIdentitySmoothAction : (G).X ⊗ (M) ⟶ (M) :=
  ((j) ⊗ₘ 𝟙 (M)) ≫ completeSmoothMul K n h

/-- On the second identity chart the action is the original identity multiplication. -/
@[reassoc] theorem completeIdentitySmoothAction_identity :
    (𝟙 (G).X ⊗ₘ (j)) ≫ completeIdentitySmoothAction K n h =
      μ[(G).X] ≫ (j) := by
  rw [completeIdentitySmoothAction, ← Category.assoc, tensorHom_comp_tensorHom,
    Category.id_comp, Category.comp_id, completeSmoothMul_chart,
    completeIdentityChartMul, zero_add]

/-- Include both original inputs into the whole identity action product. -/
def completeIdentitySmoothActionInput :
    ((G).X ⊗ (M)).left ⟶ completeIdentityActionProduct K n h 0 :=
  pullback.lift (pullback.fst (G).X.hom (M).hom)
    (pullback.snd (G).X.hom (M).hom ≫ (π).smoothLocus.ι) (by
      have he : pullback.fst (G).X.hom (M).hom ≫ (G).X.hom =
          pullback.snd (G).X.hom (M).hom ≫ (π).smoothLocus.ι ≫ (π) :=
        pullback.condition
      exact he.trans (Category.assoc _ _ _).symm)

/-- The input map keeps the original first identity coordinate. -/
@[reassoc] theorem completeIdentitySmoothActionInput_fst :
    completeIdentitySmoothActionInput K n h ≫ pullback.fst _ _ =
      pullback.fst (G).X.hom (M).hom := pullback.lift_fst _ _ _

/-- The input map keeps the entire original smooth second input. -/
@[reassoc] theorem completeIdentitySmoothActionInput_snd :
    completeIdentitySmoothActionInput K n h ≫ pullback.snd _ _ =
      pullback.snd (G).X.hom (M).hom ≫ (π).smoothLocus.ι := pullback.lift_snd _ _ _

/-- Restricting the second input to the identity chart retains the original pair inclusion. -/
@[reassoc] theorem completeIdentitySmoothActionInput_identity :
    (𝟙 (G).X ⊗ₘ (j)).left ≫ completeIdentitySmoothActionInput K n h =
      completeIdentityPairToAction K n h 0 := by
  apply pullback.hom_ext
  · rw [Category.assoc, completeIdentitySmoothActionInput_fst,
      completeIdentityPairToAction_fst]
    have he := congrArg Over.Hom.left (tensorHom_fst (𝟙 (G).X) (j))
    change (𝟙 (G).X ⊗ₘ (j)).left ≫ pullback.fst (G).X.hom (M).hom =
      pullback.fst (G).X.hom (G).X.hom ≫ 𝟙 _ at he
    simpa only [Category.comp_id] using he
  · rw [Category.assoc, completeIdentitySmoothActionInput_snd,
      completeIdentityPairToAction_snd]
    have he := congrArg Over.Hom.left (tensorHom_snd (𝟙 (G).X) (j))
    change (𝟙 (G).X ⊗ₘ (j)).left ≫ pullback.snd (G).X.hom (M).hom =
      pullback.snd (G).X.hom (G).X.hom ≫ (j).left at he
    rw [← Category.assoc, he, Category.assoc, completeIdentityChart_zero_inclusion]

end FLT.Mazur.PolygonInfinitesimalStages
