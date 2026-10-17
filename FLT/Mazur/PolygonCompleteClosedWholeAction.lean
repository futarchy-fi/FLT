/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedLaurentComparison
public import FLT.Mazur.FiniteCoproductTensorRight

/-!
# The complete whole action specializes to the original full polygon action

The actual Cartesian closed product retains the original split smooth parameter
and the entire original polygon. Laurent components glue to equality of the
full action maps, without restricting the parameter to field-valued points.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "C" => PolygonCyclicAtlas.polygon K n h
local notation "G" => PolygonSplitGroup.model K n
local notation "M" => completeOriginalSmoothOver K n h
local notation "X" => completeOriginalWholeOver K n h
local notation "P" => PolygonCyclicAtlas.normalization K n h
local notation "Q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn
local notation "j" => completeClosedFiberInclusion K n h
local notation "b" => completeClosedBase K
local notation "hb" => completeClosedFiber_isPullback K n h
local notation "I" => completeClosedActionInput K n h
local notation "a" => completeWholeAction K n h

/-- The actual full closed action input has the unchanged residue-field coefficient map. -/
theorem completeClosedWholeAction_base :
    (I) ≫ (a).left ≫ (X).hom = ((G) ⊗ (C)).hom ≫ (b) := by
  rw [(a).w, ← (snd (M) (X)).w, completeClosedActionInput_snd_assoc]
  have hw : (j) ≫ (X).hom = (C).hom ≫ (b) := (hb).w
  rw [hw, ← Category.assoc, (snd (G) (C)).w]

/-- The original action lifted to its actual closed polygon by the Cartesian square. -/
def completeClosedWholeAction : (G) ⊗ (C) ⟶ (C) :=
  Over.homMk ((hb).lift ((I) ≫ (a).left) (((G) ⊗ (C)).hom)
    (completeClosedWholeAction_base K n h)) ((hb).lift_snd _ _ _)

/-- The lift retains the actual complete whole action on its unchanged original input. -/
@[reassoc] theorem completeClosedWholeAction_inclusion :
    (completeClosedWholeAction K n h).left ≫ (j) = (I) ≫ (a).left :=
  (hb).lift_fst _ _ _

/-- The entire original closed action is the pre-existing universal polygon action. -/
theorem completeClosedWholeAction_eq :
    completeClosedWholeAction K n h = PolygonUniversalAction.act K n hn P Q hp := by
  apply FiniteCoproductTensorRight.hom_ext
    (fun _ : ZMod n ↦ MultiplicativeGroupScheme.gm K) (C)
  intro label
  obtain ⟨i, rfl⟩ := (ZMod.finEquiv n).surjective label
  apply Over.OverMorphism.ext
  apply (cancel_mono (j)).mp
  apply (cancel_epi (completeClosedLaurentProductIso K n h).hom).mp
  change _ ≫ (PolygonSplitGroup.component K n (ZMod.finEquiv n i) ⊗ₘ 𝟙 (C)).left ≫
    (completeClosedWholeAction K n h).left ≫ (j) = _
  rw [completeClosedWholeAction_inclusion, completeClosedActionInput_laurent_assoc]
  exact completeWholeAction_closedLaurent_comparison K n h i

/-- The full old split smooth-by-whole action agrees in the original complete polygon. -/
@[reassoc] theorem completeWholeAction_closed :
    completeClosedActionInput K n h ≫ (completeWholeAction K n h).left =
      (PolygonUniversalAction.act K n hn P Q hp).left ≫ completeClosedFiberInclusion K n h := by
  rw [← completeClosedWholeAction_eq, completeClosedWholeAction_inclusion]

end FLT.Mazur.PolygonInfinitesimalStages
