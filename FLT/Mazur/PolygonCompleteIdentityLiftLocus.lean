/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFlatOpenLift

/-!
# The exact open domain of the original polygon-valued action

Every actual local lift makes the full original graph invertible over its
domain. Consequently the constructed flat target open is the largest open
on which the prescribed cubic action lifts to the original polygon.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "P" => completeIdentityActionProduct K n h 0
local notation "p" => completeIdentityActionGraphProjection K n h
local notation "l" => completeIdentityActionGraphLift K n h
local notation "c" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "a" => completeIdentityActionTarget K n h (0 : Fin n)
local notation "s" => completeIdentityActionSecond K n h
local notation "π" => exactVeroneseProjToBase K n h
/-- Any actual local lift determines the polygon map on the entire graph above its domain. -/
theorem completeIdentityActionLocalLift_graph
    (W : (completeIdentityActionProduct K n h 0).Opens)
    (F : W.toScheme ⟶ exactVeroneseProj K n h) (hF : F ≫ (c) = W.ι ≫ (a)) :
    pullback.fst (p) W.ι ≫ (l) = pullback.snd (p) W.ι ≫ F := by
  apply completeFlat_contraction_ext K n h 0 ((pullback.fst (p) W.ι) ≫ (p) ≫ (s) ≫ (π))
  · rw [Category.assoc, completeIdentityActionGraphLift_structure]
  · rw [Category.assoc, completeIdentityActionLift_structure K n h W.ι F hF,
      pullback.condition_assoc]
  · rw [Category.assoc, completeIdentityActionGraphLift_contraction,
      pullback.condition_assoc, Category.assoc, hF]

/-- A genuine original-input lift rules out all exceptional graph structure over its open. -/
theorem completeIdentityActionLocalLift_graph_isIso
    (W : (completeIdentityActionProduct K n h 0).Opens)
    (F : W.toScheme ⟶ exactVeroneseProj K n h) (hF : F ≫ (c) = W.ι ≫ (a)) :
    IsIso (pullback.snd (p) W.ι) := by
  have hl := completeIdentityActionLocalLift_graph K n h W F hF
  let _ : Mono (pullback.snd (p) W.ι) := by
    constructor
    intro T f g he
    apply (cancel_mono (pullback.fst (p) W.ι)).mp
    apply (cancel_mono (completeIdentityActionGraphInclusion K n h)).mp
    apply pullback.hom_ext
    · change (f ≫ (pullback.fst (p) W.ι)) ≫ (p) = (g ≫ (pullback.fst (p) W.ι)) ≫ (p)
      simp only [Category.assoc, pullback.condition]
      rw [← Category.assoc, he, Category.assoc]
    · change (f ≫ (pullback.fst (p) W.ι)) ≫ (l) = (g ≫ (pullback.fst (p) W.ι)) ≫ (l)
      rw [Category.assoc, hl, ← Category.assoc, he, Category.assoc, ← hl, Category.assoc]
  let _ : IsClosedImmersion (pullback.snd (p) W.ι) :=
    (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨inferInstance, inferInstance⟩
  exact IsClosedImmersion.isIso_iff_ker_eq_bot.mpr (Scheme.Hom.ker_eq_bot _)

/-- The constructed open is exactly the largest domain of an original polygon-valued lift. -/
theorem completeIdentityAction_le_flatOpen_iff_exists
    (W : (completeIdentityActionProduct K n h 0).Opens) :
    W ≤ completeIdentityActionFlatOpen K n h ↔
      ∃ F : W.toScheme ⟶ exactVeroneseProj K n h, F ≫ (c) = W.ι ≫ (a) := by
  constructor
  · intro hW
    refine ⟨(P).homOfLE hW ≫ completeIdentityActionFlatLift K n h, ?_⟩
    rw [Category.assoc, completeIdentityActionFlatLift_contraction,
      ← Category.assoc, Scheme.homOfLE_ι]
  · rintro ⟨F, hF⟩
    let _ := completeIdentityActionLocalLift_graph_isIso K n h W F hF
    exact (SchemeFlatTargetOpen.le_locus_iff (p) W).mpr inferInstance

/-- The full original action exists exactly when the constructed domain covers every input. -/
theorem completeIdentityActionFlatOpen_eq_top_iff_nodeCharts :
    completeIdentityActionFlatOpen K n h = ⊤ ↔
      ∀ i : Fin n, completeIdentityActionExtensionOpen K n h (some i) ≤
        completeIdentityActionFlatOpen K n h := by
  constructor
  · intro ht i
    rw [ht]
    exact le_top
  · intro hn
    apply top_le_iff.mp
    intro x _
    obtain ⟨i, hi⟩ := completeActionExtensionOpen_cover K n h
      (completeIdentityActionSecond K n h x)
    cases i with
    | none => exact completeIdentityActionSmooth_le_flatOpen K n h hi
    | some i => exact hn i hi

end FLT.Mazur.PolygonInfinitesimalStages
