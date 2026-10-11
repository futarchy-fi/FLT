/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteMarkedCoordinateGeneration

/-!
# Original closed-stage detection of complete line isomorphisms

A morphism between actual line bundles is invertible wherever its closed
restriction is invertible: properness over the local base detects the cover
by the isomorphism open. No inverse morphism is assumed in the input.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] originalStageToCompatibleProj exactVeroneseProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- An open containing the entire original zero stage is the entire complete family. -/
theorem completeOpen_eq_top_of_originalZero (U : (exactVeroneseProj K n h).Opens)
    (hU : originalStageToCompatibleProj K n h 0 ⁻¹ᵁ U = ⊤) : U = ⊤ := by
  have hc := completeOpenCover_of_originalZero K n h (fun _ : Unit ↦ U)
    (by simpa only [iSup_const] using hU)
  simpa only [iSup_const] using hc

/-- A complete line morphism is invertible if its actual original zero-stage pullback is. -/
theorem completeLineHom_isIso_of_originalZero
    {L M : (exactVeroneseProj K n h).Modules}
    (hL : LocallyFreeRankOne L) (hM : LocallyFreeRankOne M) (a : L ⟶ M)
    [IsIso ((pullback (originalStageToCompatibleProj K n h 0)).map a)] : IsIso a := by
  have hopen : moduleHomIsoOpen a = ⊤ := by
    apply completeOpen_eq_top_of_originalZero K n h
    rw [← moduleHomIsoOpen_pullback a hL hM]
    exact top_unique (le_moduleHomIsoOpen _ ⊤)
  apply ModuleSheafOpenIsoDetection.isIso_of_openCover a
    (fun _ : Unit ↦ moduleHomIsoOpen a)
  · intro x
    exact ⟨(), by rw [hopen]; trivial⟩
  · intro _
    infer_instance

end FLT.Mazur.PolygonInfinitesimalStages
