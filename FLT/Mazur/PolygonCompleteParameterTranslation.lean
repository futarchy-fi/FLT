/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteWholeShear

/-!
# Original whole-polygon translations over arbitrary parameter schemes

A smooth point over any original relative test scheme acts on the entire
base-changed original polygon. No flatness or reducedness is required.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local instance] completeSmoothGrpObj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "M" => completeOriginalSmoothOver K n h
local notation "X" => completeOriginalWholeOver K n h
local notation "a" => completeWholeAction K n h
variable {T : Over (Spec (.of (PowerSeries K)))}

/-- Translation on the actual original polygon pulled back to the parameter scheme. -/
def completeParameterTranslation (g : T ⟶ (M)) : (X) ⊗ T ⟶ (X) ⊗ T :=
  lift (lift (snd _ _ ≫ g) (fst _ _) ≫ (a)) (snd _ _)

/-- Translation evaluates by the original full action on every relative point. -/
@[reassoc] theorem completeParameterTranslation_evaluation (g : T ⟶ (M))
    {U : Over (Spec (.of (PowerSeries K)))} (x : U ⟶ (X)) (t : U ⟶ T) :
    lift x t ≫ completeParameterTranslation K n h g =
      lift (lift (t ≫ g) x ≫ (a)) t := by
  simp only [completeParameterTranslation, comp_lift, comp_lift_assoc,
    lift_snd, lift_snd_assoc, lift_fst]

/-- Translation preserves the actual new parameter base. -/
@[reassoc] theorem completeParameterTranslation_snd (g : T ⟶ (M)) :
    completeParameterTranslation K n h g ≫ snd (X) T = snd _ _ := lift_snd _ _

/-- Multiplying varying parameters composes their original whole translations. -/
theorem completeParameterTranslation_mul (g k : T ⟶ (M)) :
    completeParameterTranslation K n h (g * k) =
      completeParameterTranslation K n h k ≫ completeParameterTranslation K n h g := by
  conv_rhs => rw [completeParameterTranslation, completeParameterTranslation_evaluation]
  unfold completeParameterTranslation
  rw [MonObj.comp_mul, completeWholeAction_associative_evaluation]

/-- The identity parameter acts identically on the whole original base change. -/
theorem completeParameterTranslation_one :
    completeParameterTranslation K n h (1 : T ⟶ (M)) = 𝟙 ((X) ⊗ T) := by
  simp only [completeParameterTranslation, MonObj.comp_one,
    completeWholeAction_unit_evaluation, lift_fst_snd]

/-- Every varying smooth parameter acts by an actual automorphism. -/
def completeParameterTranslationIso (g : T ⟶ (M)) : (X) ⊗ T ≅ (X) ⊗ T where
  hom := completeParameterTranslation K n h g
  inv := completeParameterTranslation K n h g⁻¹
  hom_inv_id := by rw [← completeParameterTranslation_mul, inv_mul_cancel,
    completeParameterTranslation_one]
  inv_hom_id := by rw [← completeParameterTranslation_mul, mul_inv_cancel,
    completeParameterTranslation_one]

/-- The underlying morphism is an isomorphism of the actual base-changed schemes. -/
instance completeParameterTranslation_left_isIso (g : T ⟶ (M)) :
    IsIso (completeParameterTranslation K n h g).left :=
  ((Over.forget _).mapIso (completeParameterTranslationIso K n h g)).isIso_hom

/-- The translation square over the unchanged parameter scheme is Cartesian. -/
theorem completeParameterTranslation_isPullback (g : T ⟶ (M)) :
    IsPullback (completeParameterTranslation K n h g).left
      (snd (X) T).left (snd (X) T).left (𝟙 T.left) := by
  apply IsPullback.of_horiz_isIso
  constructor
  simpa only [Category.comp_id, Over.comp_left] using
    congrArg Over.Hom.left (completeParameterTranslation_snd K n h g)

end FLT.Mazur.PolygonInfinitesimalStages
