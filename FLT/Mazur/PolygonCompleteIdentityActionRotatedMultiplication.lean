/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentitySmoothActionEquivariance

/-!
# Original identity multiplication controls every rotated smooth input

Translate only the second identity input into an arbitrary original chart.
The whole-domain cubic target is the original identity multiplication
followed by that same original rotation and contraction.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeRotation
attribute [local instance] exactVeroneseProjToBase_lfp
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (b : ZMod n)
local notation "G" => completePointOriginalBaseGroup K n h (0 : Fin n)
local notation "U" => completePointIdentityOpen K n h (0 : Fin n)
local notation "π" => exactVeroneseProjToBase K n h
local notation "j" => completeIdentityChart K n h 0 b

/-- Restriction of the original smooth action to any original second-parameter chart. -/
theorem completeIdentitySmoothAction_chart :
    (𝟙 (G).X ⊗ₘ (j)) ≫ completeIdentitySmoothAction K n h = μ[(G).X] ≫ (j) := by
  rw [completeIdentitySmoothAction, ← Category.assoc, tensorHom_comp_tensorHom,
    Category.id_comp, Category.comp_id, completeSmoothMul_chart,
    completeIdentityChartMul, zero_add]

/-- The original pair included in the full action input after rotating its second coordinate. -/
def completeIdentityRotatedPairToAction :
    ((G).X ⊗ (G).X).left ⟶ completeIdentityActionProduct K n h 0 :=
  (𝟙 (G).X ⊗ₘ (j)).left ≫ completeIdentitySmoothActionInput K n h

/-- Rotation leaves the original first identity parameter unchanged. -/
@[reassoc] theorem completeIdentityRotatedPairToAction_fst :
    completeIdentityRotatedPairToAction K n h b ≫ pullback.fst (G).X.hom (π) =
      pullback.fst (G).X.hom (G).X.hom := by
  rw [completeIdentityRotatedPairToAction, Category.assoc,
    completeIdentitySmoothActionInput_fst]
  have he := congrArg Over.Hom.left (tensorHom_fst (𝟙 (G).X) (j))
  change (𝟙 (G).X ⊗ₘ (j)).left ≫ pullback.fst _ _ =
    pullback.fst (G).X.hom (G).X.hom ≫ 𝟙 _ at he
  simpa only [Category.comp_id] using he

/-- The second parameter retains its actual original inclusion and rotation. -/
@[reassoc] theorem completeIdentityRotatedPairToAction_snd :
    completeIdentityRotatedPairToAction K n h b ≫ pullback.snd (G).X.hom (π) =
      pullback.snd (G).X.hom (G).X.hom ≫ (U).ι ≫ completeRotation K n h b := by
  rw [completeIdentityRotatedPairToAction, Category.assoc,
    completeIdentitySmoothActionInput_snd]
  have he := congrArg Over.Hom.left (tensorHom_snd (𝟙 (G).X) (j))
  change (𝟙 (G).X ⊗ₘ (j)).left ≫ pullback.snd _ _ =
    pullback.snd (G).X.hom (G).X.hom ≫ (j).left at he
  rw [← Category.assoc, he, Category.assoc, completeIdentityChart_inclusion]

/-- The prescribed cubic target on every rotated chart is the actual original multiplication. -/
@[reassoc] theorem completeIdentityRotatedPairToAction_target :
    completeIdentityRotatedPairToAction K n h b ≫ completeIdentityActionTarget K n h 0 =
      (μ[(G).X]).left ≫ (U).ι ≫ completeRotation K n h b ≫
        completePointToIntegralCubic K n h 0 := by
  rw [completeIdentityRotatedPairToAction, Category.assoc,
    ← completeIdentitySmoothAction_contraction]
  have he := congrArg Over.Hom.left (completeIdentitySmoothAction_chart K n h b)
  change (𝟙 (G).X ⊗ₘ (j)).left ≫ (completeIdentitySmoothAction K n h).left =
    (μ[(G).X]).left ≫ (j).left at he
  rw [← Category.assoc _ (completeIdentitySmoothAction K n h).left _, he,
    Category.assoc, completeIdentityChart_inclusion_assoc]

end FLT.Mazur.PolygonInfinitesimalStages
