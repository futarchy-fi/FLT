/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteParameterTranslation
public import FLT.Mazur.PolygonCompleteMarkingLineBaseChange
public import FLT.Mazur.SectionCartesianKernel

/-!
# Moved original marking divisors over arbitrary parameter schemes

Translation moves each original labeled section. The complete product of its
scheme-theoretic ideals stays relative Cartier on the actual whole base change.
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
variable {T : Over (Spec (.of (PowerSeries K)))}

/-- The full original marking ideal on the actual parameter base change. -/
def completeParameterMarkingIdeal : ((X) ⊗ T).left.IdealSheafData :=
  (completeMarkingDivisor K n h).comap (fst (X) T).left

/-- The full original parameter marking remains relative Cartier over arbitrary bases. -/
theorem completeParameterMarkingIdeal_cartier :
    RelativeEffectiveCartier (snd (X) T).left (completeParameterMarkingIdeal K n h) :=
  relativeCartierBaseChange _ T.hom _ (completeMarkingDivisor_relativeCartier K n h)

/-- Translation moves each actual original labeled section, including on nonreduced bases. -/
def completeParameterMovedMarking (g : T ⟶ (M)) (i : Fin n) :
    T.left ⟶ ((X) ⊗ T).left :=
  completeFiberMarking K n h T.hom i ≫ (completeParameterTranslation K n h g).left

/-- Every moved marking is a section over the unchanged parameter scheme. -/
@[reassoc] theorem completeParameterMovedMarking_snd (g : T ⟶ (M)) (i : Fin n) :
    completeParameterMovedMarking K n h g i ≫ (snd (X) T).left = 𝟙 _ := by
  rw [completeParameterMovedMarking, Category.assoc,
    ← Over.comp_left, completeParameterTranslation_snd]
  exact completeFiberMarking_snd K n h T.hom i

/-- Transport the complete original ideal, rather than just its support. -/
def completeParameterMovedIdeal (g : T ⟶ (M)) : ((X) ⊗ T).left.IdealSheafData :=
  (completeParameterMarkingIdeal K n h).comap
    (completeParameterTranslation K n h g⁻¹).left

/-- The transported ideal is relative Cartier over the actual parameter scheme. -/
theorem completeParameterMovedIdeal_cartier (g : T ⟶ (M)) :
    RelativeEffectiveCartier (snd (X) T).left (completeParameterMovedIdeal K n h g) := by
  have hc := (completeParameterMarkingIdeal_cartier K n h (T := T)).comap_of_isOpenImmersion
    (completeParameterTranslation K n h g⁻¹).left
  rw [← Over.comp_left, completeParameterTranslation_snd] at hc
  exact hc

/-- Pulling the moved ideal back by its translation returns the original full ideal. -/
theorem completeParameterMovedIdeal_pullback (g : T ⟶ (M)) :
    (completeParameterMovedIdeal K n h g).comap
      (completeParameterTranslation K n h g).left = completeParameterMarkingIdeal K n h := by
  rw [completeParameterMovedIdeal, ← Scheme.IdealSheafData.comap_comp,
    ← Over.comp_left, ← completeParameterTranslation_mul, inv_mul_cancel,
    completeParameterTranslation_one, Over.id_left, Scheme.IdealSheafData.comap_id]

/-- The transported ideal is exactly the product of the actual moved marking kernels. -/
theorem completeParameterMovedIdeal_eq_prod (g : T ⟶ (M)) :
    completeParameterMovedIdeal K n h g =
      ∏ i : Fin n, (completeParameterMovedMarking K n h g i).ker := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsSeparated (snd (X) T).left := inferInstanceAs
    (IsSeparated (pullback.snd (exactVeroneseProjToBase K n h) T.hom))
  have hp := section_prod_comap_of_cartesian
    (completeParameterTranslation_isPullback K n h g⁻¹) Finset.univ
    (completeParameterMovedMarking K n h g) (completeFiberMarking K n h T.hom)
    (completeParameterMovedMarking_snd K n h g)
    (completeFiberMarking_snd K n h T.hom) (fun i ↦ by
      rw [completeParameterMovedMarking, Category.assoc, ← Over.comp_left,
        ← completeParameterTranslation_mul, inv_mul_cancel,
        completeParameterTranslation_one, Over.id_left]
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  change ((completeMarkingDivisor K n h).comap
    (pullback.fst (exactVeroneseProjToBase K n h) T.hom)).comap _ = _
  rw [completeMarkingDivisor_comap]
  exact hp

end FLT.Mazur.PolygonInfinitesimalStages
