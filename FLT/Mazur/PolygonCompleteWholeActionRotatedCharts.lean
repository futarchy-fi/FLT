/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteWholeActionParameterCover
public import FLT.Mazur.PolygonCompleteIdentityWholeActionRotation

/-!
# Whole-polygon actions on every original rotated parameter chart

Rotating the output of the constructed identity action gives a whole-polygon
map on every original smooth parameter chart. Its smooth restriction is the
already constructed original smooth multiplication.
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
local notation "X" => completeOriginalWholeOver K n h
local notation "π" => exactVeroneseProjToBase K n h
local notation "j" => completeWholeSmoothInclusion K n h
local notation "a" => completeIdentityWholeActionOver K n h

/-- The original complete rotation viewed over its unchanged base. -/
def completeWholeRotationOver (b : ZMod n) : (X) ⟶ (X) :=
  Over.homMk (completeRotation K n h b) (completeRotation_toBase K n h b)

/-- Every original parameter chart now acts on the entire original polygon. -/
def completeWholeActionChart (b : ZMod n) : (G).X ⊗ (X) ⟶ (X) :=
  (a) ≫ completeWholeRotationOver K n h b

/-- The relative identity action retains the full original smooth multiplication. -/
@[reassoc] theorem completeIdentityWholeActionOver_smooth :
    (𝟙 (G).X ⊗ₘ (j)) ≫ (a) = completeIdentitySmoothAction K n h ≫ (j) := by
  apply Over.OverMorphism.ext
  have he : (𝟙 (G).X ⊗ₘ (j)).left = completeIdentitySmoothActionInput K n h := by
    apply pullback.hom_ext <;>
      simp only [completeOriginalWholeOver, Over.mk_hom, Over.tensorHom_left,
        pullback.map, pullback.lift_fst, pullback.lift_snd,
        Over.id_left, Category.comp_id, completeWholeSmoothInclusion, Over.homMk_left,
        completeIdentitySmoothActionInput_fst, completeIdentitySmoothActionInput_snd]
  change (𝟙 (G).X ⊗ₘ (j)).left ≫ completeIdentityWholeAction K n h = _
  rw [he]
  exact completeIdentityWholeAction_smoothInput K n h

/-- On relative test points, rotation of the first chart rotates the smooth action output. -/
theorem completeWholeActionChart_smooth_evaluation (b : ZMod n)
    {T : Over (Spec (.of (PowerSeries K)))} (x : T ⟶ (G).X) (y : T ⟶ (M)) :
    lift (x ≫ completeIdentityChart K n h 0 b) y ≫ completeSmoothMul K n h =
      (lift x y ≫ completeIdentitySmoothAction K n h) ≫
        translation (completeOriginalSmoothCyclicPoint K n h b) := by
  have hj : completeIdentityChart K n h 0 b =
      completeIdentityChart K n h 0 0 ≫
        translation (completeOriginalSmoothCyclicPoint K n h b) := by
    simpa only [add_zero] using (completeIdentityChart_translation K n h b 0).symm
  change (x ≫ completeIdentityChart K n h 0 b) * y = _
  rw [completeIdentitySmoothAction_evaluation, comp_translation]
  rw [hj, ← Category.assoc x, comp_translation, _root_.mul_assoc]

/-- The first-chart smooth product is the rotation of the original identity smooth action. -/
theorem completeWholeActionChart_smooth_mul (b : ZMod n) :
    (completeIdentityChart K n h 0 b ⊗ₘ 𝟙 (M)) ≫ completeSmoothMul K n h =
      completeIdentitySmoothAction K n h ≫
        translation (completeOriginalSmoothCyclicPoint K n h b) := by
  have he := completeWholeActionChart_smooth_evaluation K n h b
    (fst (G).X (M)) (snd (G).X (M))
  rw [← lift_fst_comp_snd_comp]
  simpa only [tensorHom_fst, tensorHom_snd, Category.comp_id,
    lift_fst_snd, Category.id_comp] using he

/-- Every whole-input rotated chart restricts to the original full smooth multiplication. -/
@[reassoc] theorem completeWholeActionChart_smooth (b : ZMod n) :
    (𝟙 (G).X ⊗ₘ (j)) ≫ completeWholeActionChart K n h b =
      (completeIdentityChart K n h 0 b ⊗ₘ 𝟙 (M)) ≫ completeSmoothMul K n h ≫ (j) := by
  rw [completeWholeActionChart, completeIdentityWholeActionOver_smooth_assoc,
    ← Category.assoc _ (completeSmoothMul K n h), completeWholeActionChart_smooth_mul,
    Category.assoc]
  congr 1
  apply Over.OverMorphism.ext
  exact (completeOriginalSmooth_translation_rotation K n h b).symm

end FLT.Mazur.PolygonInfinitesimalStages
