/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedWholeAction
public import FLT.Mazur.PolygonCompleteClosedParameterSection
public import FLT.Mazur.PolygonParameterTranslationInput

/-!
# Arbitrary original translations equal the complete-family translations

The comparison uses the unmoved whole-polygon product and the unchanged
varying smooth parameter. No reducedness or flatness of the parameter scheme
is required, and all original polygon nodes are retained.
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
local notation "M" => completeOriginalSmoothOver K n h
local notation "X" => completeOriginalWholeOver K n h
local notation "B" => Over.mk (g ≫ completeClosedBase K)
local notation "CX" => Functor.obj (Over.pullback g) (C)
local notation "P" => PolygonCyclicAtlas.normalization K n h
local notation "Q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn
variable (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (PolygonSplitGroup.model K n))
local notation "s" => completeClosedParameterSection K n h g c
local notation "e" => completeUnmovedBoundaryProductIso K n h g
local notation "τ" => translationIso K n hn P Q hp g c
local notation "I" => translationInput K n g c

/-- The actual complete translation input is the original full closed action input. -/
@[reassoc] theorem completeClosedTranslation_input :
    (e).hom ≫ (lift (snd (X) (B) ≫ (s)) (fst (X) (B))).left =
      (I) ≫ completeClosedActionInput K n h := by
  have hf := congrArg Over.Hom.left (lift_fst (snd (X) (B) ≫ (s)) (fst (X) (B)))
  have hs := congrArg Over.Hom.left (lift_snd (snd (X) (B) ≫ (s)) (fst (X) (B)))
  simp only [Over.comp_left] at hf hs
  apply pullback.hom_ext
  · change _ ≫ (fst (M) (X)).left = _ ≫ (fst (M) (X)).left
    rw [Category.assoc, hf, completeUnmovedBoundaryProductIso_snd_assoc,
      Category.assoc, completeClosedActionInput_fst, translationInput_fst_assoc,
      completeClosedParameterSection_left]
  · change _ ≫ (snd (M) (X)).left = _ ≫ (snd (M) (X)).left
    rw [Category.assoc, hs, completeUnmovedBoundaryProductIso_fst,
      Category.assoc, completeClosedActionInput_snd, translationInput_snd_assoc]
    rfl

/-- Arbitrary original varying translations intertwine under the unmoved product comparison. -/
@[reassoc] theorem completeClosedTranslation_hom :
    (τ).hom.left ≫ (e).hom =
      (e).hom ≫ (completeParameterTranslation K n h (s)).left := by
  have hf := congrArg Over.Hom.left
    (lift_fst (lift (snd (X) (B) ≫ (s)) (fst (X) (B)) ≫ completeWholeAction K n h)
      (snd (X) (B)))
  change (completeParameterTranslation K n h (s)).left ≫ (fst (X) (B)).left =
    (lift (snd (X) (B) ≫ (s)) (fst (X) (B))).left ≫
      (completeWholeAction K n h).left at hf
  have hs := congrArg Over.Hom.left (completeParameterTranslation_snd K n h (s))
  simp only [Over.comp_left] at hs
  apply pullback.hom_ext
  · change _ ≫ (fst (X) (B)).left = _ ≫ (fst (X) (B)).left
    rw [Category.assoc, completeUnmovedBoundaryProductIso_fst, Category.assoc, hf,
      completeClosedTranslation_input_assoc, completeWholeAction_closed]
    change (τ).hom.left ≫ pullback.fst (C).hom g ≫ completeClosedFiberInclusion K n h = _
    rw [translationIso_hom_projection_assoc]
  · change _ ≫ (snd (X) (B)).left = _ ≫ (snd (X) (B)).left
    rw [Category.assoc, completeUnmovedBoundaryProductIso_snd, Over.w, Category.assoc, hs,
      completeUnmovedBoundaryProductIso_snd]

end FLT.Mazur.PolygonInfinitesimalStages
