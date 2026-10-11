/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteLineHomReconstruction
public import FLT.Mazur.PolygonCompleteLineIsoDetection

/-!
# Reconstructing original compatible complete-line isomorphisms

Formal reconstruction supplies the actual morphism. Its original closed
restriction is invertible, so properness proves global invertibility.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] originalStageToCompatibleProj exactVeroneseProj family
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Compatible original line isomorphisms reconstruct uniquely on the complete family. -/
theorem completeLineIso_existsUnique {L M : (exactVeroneseProj K n h).Modules}
    (hL : LocallyFreeRankOne L) (hM : LocallyFreeRankOne M)
    (a : ∀ m, (pullback (originalStageToCompatibleProj K n h m)).obj L ≅
      (pullback (originalStageToCompatibleProj K n h m)).obj M)
    (ha : ∀ {i j : ℕ} (f : i ⟶ j),
      (pullback ((stageSystem K n h).map f)).map (a j).hom ≫
          (completeLineStageTransitionIso K n h M f).hom =
        (completeLineStageTransitionIso K n h L f).hom ≫ (a i).hom) :
    ∃! b : L ≅ M, ∀ m, (pullback (originalStageToCompatibleProj K n h m)).mapIso b = a m := by
  obtain ⟨b, hb, _⟩ := completeLineHom_existsUnique K n h hL hM (fun m ↦ (a m).hom) ha
  have : IsIso ((pullback (originalStageToCompatibleProj K n h 0)).map b) := by
    rw [hb]
    infer_instance
  let _ := completeLineHom_isIso_of_originalZero K n h hL hM b
  refine ⟨asIso b, fun m ↦ Iso.ext (hb m), ?_⟩
  intro c hc
  apply completeLineIso_ext_stages K n h hL hM
  intro m
  exact (hc m).trans (Iso.ext (hb m)).symm

end FLT.Mazur.PolygonInfinitesimalStages
