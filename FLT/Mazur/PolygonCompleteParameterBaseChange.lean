/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteParameterMarkingLine

/-!
# Original varying translations and markings commute with base change

The actual product map intertwines translations. The full moved marking ideal,
with its multiplicities, pulls back to the corresponding moved ideal.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local instance] completeSmoothGrpObj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "M" => completeOriginalSmoothOver K n h
local notation "X" => completeOriginalWholeOver K n h
variable {U T : Over (Spec (.of (PowerSeries K)))} (f : U ⟶ T)

/-- The actual change-of-parameter map intertwines the original whole translations. -/
theorem completeParameterTranslation_baseChange (g : T ⟶ (M)) :
    (𝟙 (X) ⊗ₘ f) ≫ completeParameterTranslation K n h g =
      completeParameterTranslation K n h (f ≫ g) ≫ (𝟙 (X) ⊗ₘ f) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, completeParameterTranslation, lift_fst,
      comp_lift_assoc, tensorHom_snd_assoc, tensorHom_fst, Category.comp_id]
  · simp only [Category.assoc, completeParameterTranslation_snd,
      tensorHom_snd, completeParameterTranslation_snd_assoc]

/-- The original full marking ideal commutes with the actual change of parameter. -/
theorem completeParameterMarkingIdeal_baseChange :
    (completeParameterMarkingIdeal K n h (T := T)).comap (𝟙 (X) ⊗ₘ f).left =
      completeParameterMarkingIdeal K n h (T := U) := by
  rw [completeParameterMarkingIdeal, ← Scheme.IdealSheafData.comap_comp,
    ← Over.comp_left, tensorHom_fst, Category.comp_id]
  rfl

/-- The moved full original marking ideal commutes with arbitrary parameter change. -/
theorem completeParameterMovedIdeal_baseChange (g : T ⟶ (M)) :
    (completeParameterMovedIdeal K n h g).comap (𝟙 (X) ⊗ₘ f).left =
      completeParameterMovedIdeal K n h (f ≫ g) := by
  rw [completeParameterMovedIdeal, ← Scheme.IdealSheafData.comap_comp,
    ← Over.comp_left, completeParameterTranslation_baseChange, Over.comp_left,
    Scheme.IdealSheafData.comap_comp, completeParameterMarkingIdeal_baseChange,
    GrpObj.comp_inv]
  rfl

/-- Every multiplicity of the moved original marking is preserved under base change. -/
theorem completeParameterMovedIdeal_power_baseChange (g : T ⟶ (M)) (d : ℕ) :
    (completeParameterMovedIdeal K n h g ^ d).comap (𝟙 (X) ⊗ₘ f).left =
      completeParameterMovedIdeal K n h (f ≫ g) ^ d := by
  rw [idealSheaf_comap_pow, completeParameterMovedIdeal_baseChange]

/-- The actual positive moved line comparison under arbitrary parameter change. -/
irreducible_def completeParameterMovedLineBaseChangeIso (g : T ⟶ (M)) :
    (Scheme.Modules.pullback (𝟙 (X) ⊗ₘ f).left).obj (completeParameterMovedLine K n h g) ≅
      completeParameterMovedLine K n h (f ≫ g) := by
  let hs := (completeParameterMovedIdeal_cartier K n h g).1
  let ht := (completeParameterMovedIdeal_cartier K n h (f ≫ g)).1
  let he := completeParameterMovedIdeal_baseChange K n h f g
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  exact divisorLinePullbackIsoOfEq _ hs ht he

/-- The actual base-change comparison retains the canonical moved marking section. -/
theorem completeParameterMovedLineBaseChangeIso_section (g : T ⟶ (M)) :
    DivisorLineSectionCompatible (𝟙 (X) ⊗ₘ f).left
      (completeParameterMovedIdeal_cartier K n h g).1
      (completeParameterMovedIdeal_cartier K n h (f ≫ g)).1
      (completeParameterMovedLineBaseChangeIso K n h f g) := by
  let hs := (completeParameterMovedIdeal_cartier K n h g).1
  let ht := (completeParameterMovedIdeal_cartier K n h (f ≫ g)).1
  let he := completeParameterMovedIdeal_baseChange K n h f g
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  rw [completeParameterMovedLineBaseChangeIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

end FLT.Mazur.PolygonInfinitesimalStages
