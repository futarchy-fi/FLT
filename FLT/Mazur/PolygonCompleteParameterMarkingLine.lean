/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteParameterMarking
public import FLT.Mazur.CartierIdealPullbackComparison

/-!
# Section-compatible lines of the varying original marking divisors

Comparisons keep track of which moved divisor is pulled back. In particular,
translation by `g` pulls the marking moved by `g*k` back to the marking moved by `k`.
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

/-- The identity parameter leaves the full original marking ideal unchanged. -/
theorem completeParameterMovedIdeal_one :
    completeParameterMovedIdeal K n h (1 : T ⟶ (M)) =
      completeParameterMarkingIdeal K n h := by
  rw [completeParameterMovedIdeal, inv_one, completeParameterTranslation_one,
    Over.id_left, Scheme.IdealSheafData.comap_id]

/-- Composition of varying parameters transports the actual complete marking ideals. -/
theorem completeParameterMovedIdeal_mul (g k : T ⟶ (M)) :
    (completeParameterMovedIdeal K n h (g * k)).comap
      (completeParameterTranslation K n h g).left = completeParameterMovedIdeal K n h k := by
  simp only [completeParameterMovedIdeal, ← Scheme.IdealSheafData.comap_comp,
    ← Over.comp_left, ← completeParameterTranslation_mul, mul_inv_rev,
    _root_.mul_assoc, inv_mul_cancel, _root_.mul_one]

/-- The positive Cartier line of the actual moved original divisor. -/
def completeParameterMovedLine (g : T ⟶ (M)) : ((X) ⊗ T).left.Modules :=
  divisorLineBundle (completeParameterMovedIdeal K n h g)
    (completeParameterMovedIdeal_cartier K n h g).1

/-- Actual line comparison for any specified product of varying original parameters. -/
irreducible_def completeParameterMovedLineIso (g k r : T ⟶ (M)) (w : g * k = r) :
    (Scheme.Modules.pullback (completeParameterTranslation K n h g).left).obj
      (completeParameterMovedLine K n h r) ≅ completeParameterMovedLine K n h k := by
  let hs := (completeParameterMovedIdeal_cartier K n h r).1
  let ht := (completeParameterMovedIdeal_cartier K n h k).1
  have he : (completeParameterMovedIdeal K n h r).comap
      (completeParameterTranslation K n h g).left = completeParameterMovedIdeal K n h k := by
    rw [← w, completeParameterMovedIdeal_mul]
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  exact divisorLinePullbackIsoOfEq _ hs ht he

/-- The comparison preserves the canonical section, not merely the line isomorphism class. -/
theorem completeParameterMovedLineIso_section (g k r : T ⟶ (M)) (w : g * k = r) :
    DivisorLineSectionCompatible (completeParameterTranslation K n h g).left
      (completeParameterMovedIdeal_cartier K n h r).1
      (completeParameterMovedIdeal_cartier K n h k).1
      (completeParameterMovedLineIso K n h g k r w) := by
  rw [completeParameterMovedLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

end FLT.Mazur.PolygonInfinitesimalStages
