/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteFlatContractionExt
public import FLT.Mazur.PolygonCompleteIdentityActionSource

/-!
# Automatic compatibility and gluing for original node-input lifts

Any constructed local lifts of the fixed cubic action automatically agree on
all overlaps. This discharges the gluing step without assuming compatibility;
existence on the original node-input charts remains a separate requirement.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "X" => exactVeroneseProj K n h
local notation "P" => completeIdentityActionProduct K n h 0
local notation "π" => exactVeroneseProjToBase K n h
local notation "s" => completeIdentityActionSecond K n h
local notation "c" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "a" => completeIdentityActionTarget K n h (0 : Fin n)

/-- Any actual local lift retains the original base, without a separate base hypothesis. -/
theorem completeIdentityActionLift_structure {T : Scheme}
    (u : T ⟶ (P)) (f : T ⟶ (X)) (hf : f ≫ (c) = u ≫ (a)) :
    f ≫ (π) = u ≫ (s) ≫ (π) := by
  apply (cancel_mono (Scheme.toSpecΓ (Spec (.of (PowerSeries K))))).mp
  simp only [Category.assoc]
  rw [← completePointToIntegralCubic_over, ← Category.assoc f, hf, Category.assoc,
    completeIdentityActionTarget_structure, completePointToIntegralCubic_over]

/-- The original contraction alone determines a lift on every flat input test scheme. -/
theorem completeIdentityActionLift_unique {T : Scheme}
    (u : T ⟶ (P)) [Flat (u ≫ (s) ≫ (π))]
    (f g : T ⟶ (X)) (hf : f ≫ (c) = u ≫ (a)) (hg : g ≫ (c) = u ≫ (a)) : f = g :=
  completeFlat_contraction_ext K n h 0 (u ≫ (s) ≫ (π)) f g
    (completeIdentityActionLift_structure K n h u f hf)
    (completeIdentityActionLift_structure K n h u g hg) (hf.trans hg.symm)

variable (C : (completeIdentityActionProduct K n h 0).OpenCover)
  (f : ∀ i, C.X i ⟶ exactVeroneseProj K n h)
  (hf : ∀ i, f i ≫ completePointToIntegralCubic K n h 0 =
    C.f i ≫ completeIdentityActionTarget K n h 0)

include hf in
/-- Actual local lifts automatically agree on all overlaps of any original-input open cover. -/
theorem completeIdentityActionLocal_overlap (i j : C.I₀) :
    pullback.fst (C.f i) (C.f j) ≫ f i = pullback.snd (C.f i) (C.f j) ≫ f j := by
  let u := pullback.fst (C.f i) (C.f j) ≫ C.f i
  let _ : Flat (u ≫ (s) ≫ (π)) := by
    dsimp only [u]
    rw [Category.assoc]
    infer_instance
  apply completeIdentityActionLift_unique K n h u
  · rw [Category.assoc, hf i, ← Category.assoc]
  · rw [Category.assoc, hf j, ← Category.assoc, ← pullback.condition]

/-- Genuine local lifts glue to a morphism on the entire original input product. -/
def completeIdentityActionGlue : (P) ⟶ (X) :=
  C.glueMorphisms f (completeIdentityActionLocal_overlap K n h C f hf)

/-- Gluing retains each original local map exactly. -/
@[reassoc] theorem completeIdentityActionGlue_chart (i : C.I₀) :
    C.f i ≫ completeIdentityActionGlue K n h C f hf = f i := C.ι_glueMorphisms _ _ i

/-- The glued map has the fixed original cubic action as its contraction. -/
@[reassoc] theorem completeIdentityActionGlue_contraction :
    completeIdentityActionGlue K n h C f hf ≫ (c) = (a) := by
  apply C.hom_ext
  intro i
  rw [completeIdentityActionGlue_chart_assoc, hf]

/-- The whole-input lift, when the local maps have been constructed, is unique. -/
theorem completeIdentityActionGlue_unique (g : (P) ⟶ (X)) (hg : g ≫ (c) = (a)) :
    g = completeIdentityActionGlue K n h C f hf := by
  apply completeIdentityActionLift_unique K n h (𝟙 (P))
  · simpa only [Category.id_comp] using hg
  · simpa only [Category.id_comp] using completeIdentityActionGlue_contraction K n h C f hf

/-- The first open extension task is exactly existence on the finitely many original node charts. -/
theorem completeIdentityActionLift_exists_iff_nodeCharts :
    (∃ F : (P) ⟶ (X), F ≫ (c) = (a)) ↔
      ∀ i : Fin n, ∃ F : (completeIdentityActionExtensionOpen K n h (some i)).toScheme ⟶ (X),
        F ≫ (c) = (completeIdentityActionExtensionOpen K n h (some i)).ι ≫ (a) := by
  constructor
  · rintro ⟨F, hF⟩ i
    refine ⟨(completeIdentityActionExtensionOpen K n h (some i)).ι ≫ F, ?_⟩
    rw [Category.assoc, hF]
  · intro hn
    choose F hF using hn
    let D := completeIdentityActionExtensionCover K n h
    let maps : ∀ i : Option (Fin n), D.X i ⟶ (X)
      | none => completeIdentityActionSmoothLift K n h
      | some i => F i
    have hm : ∀ i, maps i ≫ (c) = D.f i ≫ (a) := by
      intro i
      cases i with
      | none => exact completeIdentityActionSmoothLift_contraction K n h
      | some i => exact hF i
    exact ⟨completeIdentityActionGlue K n h D maps hm,
      completeIdentityActionGlue_contraction K n h D maps hm⟩

end FLT.Mazur.PolygonInfinitesimalStages
