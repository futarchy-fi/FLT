/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteWholeActionLaws

/-!
# The original whole action on arbitrary relative test points

The global morphism laws hold on every test scheme, including nonflat tests.
Each original smooth section therefore acts by an actual polygon automorphism.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeRotation
attribute [local instance] exactVeroneseProjToBase_lfp completeSmoothGrpObj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "M" => completeOriginalSmoothOver K n h
local notation "X" => completeOriginalWholeOver K n h
local notation "a" => completeWholeAction K n h

/-- The full action is associative on all relative test points, without a flatness assumption. -/
theorem completeWholeAction_associative_evaluation {T : Over (Spec (.of (PowerSeries K)))}
    (x y : T ⟶ (M)) (z : T ⟶ (X)) :
    lift (x * y) z ≫ (a) = lift x (lift y z ≫ (a)) ≫ (a) := by
  change lift (lift x y ≫ completeSmoothMul K n h) z ≫ (a) = _
  have he := congrArg (lift (lift x y) z ≫ ·) (completeWholeAction_assoc K n h)
  simpa only [← Category.assoc, lift_whiskerRight, lift_lift_associator_hom,
    lift_whiskerLeft] using he

/-- The original identity acts identically on all relative test points. -/
theorem completeWholeAction_unit_evaluation {T : Over (Spec (.of (PowerSeries K)))}
    (z : T ⟶ (X)) : lift (1 : T ⟶ (M)) z ≫ (a) = z := by
  change lift (toUnit T ≫ completeSmoothOne K n h) z ≫ (a) = z
  have he := congrArg (z ≫ ·) (completeWholeAction_unit K n h)
  simp only [comp_lift_assoc, Category.comp_id] at he
  simpa only [← Category.assoc, comp_toUnit] using he

/-- Translation by any actual smooth section of the original family. -/
def completeWholeTranslation (x : 𝟙_ (Over (Spec (.of (PowerSeries K)))) ⟶ (M)) :
    (X) ⟶ (X) := lift (toUnit (X) ≫ x) (𝟙 (X)) ≫ (a)

/-- Translation evaluated at an arbitrary original relative point. -/
@[reassoc] theorem completeWholeTranslation_evaluation
    (x : 𝟙_ (Over (Spec (.of (PowerSeries K)))) ⟶ (M))
    {T : Over (Spec (.of (PowerSeries K)))} (z : T ⟶ (X)) :
    z ≫ completeWholeTranslation K n h x = lift (toUnit T ≫ x) z ≫ (a) := by
  rw [completeWholeTranslation, comp_lift_assoc, Category.comp_id,
    ← Category.assoc, comp_toUnit]

/-- Successive translations multiply their actual original smooth parameters. -/
theorem completeWholeTranslation_mul
    (x y : 𝟙_ (Over (Spec (.of (PowerSeries K)))) ⟶ (M)) :
    completeWholeTranslation K n h (x * y) =
      completeWholeTranslation K n h y ≫ completeWholeTranslation K n h x := by
  rw [completeWholeTranslation_evaluation]
  have he := completeWholeAction_associative_evaluation K n h
    (toUnit (X) ≫ x) (toUnit (X) ≫ y) (𝟙 (X))
  simpa only [completeWholeTranslation, MonObj.comp_mul] using he

/-- The identity section gives the identity polygon automorphism. -/
theorem completeWholeTranslation_one : completeWholeTranslation K n h 1 = 𝟙 (X) := by
  simpa only [completeWholeTranslation, MonObj.comp_one] using
    completeWholeAction_unit_evaluation K n h (𝟙 (X))

/-- Every smooth section acts invertibly on the entire original polygon. -/
def completeWholeTranslationIso
    (x : 𝟙_ (Over (Spec (.of (PowerSeries K)))) ⟶ (M)) : (X) ≅ (X) where
  hom := completeWholeTranslation K n h x
  inv := completeWholeTranslation K n h x⁻¹
  hom_inv_id := by rw [← completeWholeTranslation_mul, inv_mul_cancel,
    completeWholeTranslation_one]
  inv_hom_id := by rw [← completeWholeTranslation_mul, mul_inv_cancel,
    completeWholeTranslation_one]

end FLT.Mazur.PolygonInfinitesimalStages
