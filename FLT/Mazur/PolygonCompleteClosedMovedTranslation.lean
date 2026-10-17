/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedTranslation
public import FLT.Mazur.PolygonCompleteBoundaryFiberLine

/-!
# The moved boundary is the actual inverse complete translation

The unchanged product comparison identifies the pre-existing moved boundary
map with inverse translation in the original complete family. This identifies
the full marking ideal, not merely its support or its closed points.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonParameterTranslation
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {T : Scheme} (g : T ⟶ Spec (.of K))
local notation "G" => PolygonSplitGroup.model K n
local notation "C" => PolygonCyclicAtlas.polygon K n h
local notation "X" => completeOriginalWholeOver K n h
local notation "B" => Over.mk (g ≫ completeClosedBase K)
local notation "P" => PolygonCyclicAtlas.normalization K n h
local notation "Q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn
variable (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (PolygonSplitGroup.model K n))
local notation "s" => completeClosedParameterSection K n h g c
local notation "e" => completeUnmovedBoundaryProductIso K n h g
local notation "τ" => translationIso K n hn P Q hp g c
local notation "v" => completeParameterTranslationIso K n h (s)

/-- The original inverse translation is the actual complete inverse on the unchanged product. -/
@[reassoc] theorem completeClosedTranslation_inv :
    (τ).inv.left ≫ (e).hom = (e).hom ≫ (v).inv.left := by
  apply (cancel_epi (τ).hom.left).mp
  rw [← Category.assoc, ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.id_comp]
  rw [completeClosedTranslation_hom_assoc]
  change (e).hom = (e).hom ≫ (v).hom.left ≫ (v).inv.left
  rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.comp_id]

/-- The pre-existing moved fiber comparison includes precisely the complete inverse translation. -/
theorem completeMovedBoundaryFiberIso_eq_translation :
    (completeMovedBoundaryFiberIso K n h g c).hom = (e).hom ≫ (v).inv.left := by
  rw [← completeClosedTranslation_inv]
  have hf : (e).hom ≫ pullback.fst (exactVeroneseProjToBase K n h)
      (g ≫ completeClosedBase K) = completeBoundaryParameterMap K n h g :=
    completeUnmovedBoundaryProductIso_fst K n h g
  have hs : (e).hom ≫ pullback.snd (exactVeroneseProjToBase K n h)
      (g ≫ completeClosedBase K) = ((Over.pullback g).obj (C)).hom :=
    completeUnmovedBoundaryProductIso_snd K n h g
  apply pullback.hom_ext
  · rw [completeMovedBoundaryFiberIso_fst, Category.assoc, hf]
    rfl
  · rw [completeMovedBoundaryFiberIso_snd, Category.assoc, hs, Over.w]

/-- The actual inverse complete translation recovers the original moved recovery map. -/
@[reassoc] theorem completeClosedInverseTranslation_recovery :
    (e).hom ≫ (v).inv.left ≫ (fst (X) (B)).left = completeMovedBoundaryMap K n h g c := by
  rw [← Category.assoc, ← completeMovedBoundaryFiberIso_eq_translation]
  exact completeMovedBoundaryFiberIso_fst K n h g c

/-- The full original fiber marking ideal pulls back to the entire moved product ideal. -/
theorem completeClosedInverseTranslation_ideal :
    (∏ i : Fin n, (completeFiberMarking K n h (g ≫ completeClosedBase K) i).ker).comap
      ((e).hom ≫ (v).inv.left) =
        movedProductMarkingIdeal K n hn P Q hp g c (fun _ ↦ 1) := by
  rw [← completeMovedBoundaryFiberIso_eq_translation]
  exact completeFiberMarking_movedBoundary K n h g c

/-- The full smoothing ideal has the same moved product under the actual complete inverse map. -/
theorem completeClosedInverseTranslation_smoothingIdeal :
    (completeMarkingDivisor K n h).comap
      ((e).hom ≫ (v).inv.left ≫ (fst (X) (B)).left) =
        movedProductMarkingIdeal K n hn P Q hp g c (fun _ ↦ 1) := by
  rw [completeClosedInverseTranslation_recovery]
  exact completeMarkingDivisor_movedBoundary K n h g c

end FLT.Mazur.PolygonInfinitesimalStages
