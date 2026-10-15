/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticComparedSectionReconstruction
public import FLT.Mazur.PolygonArithmeticLineIsoDetection

/-!
# Actual lifts of compatible arithmetic coordinate sections

The unique formal reconstruction is chosen once and retains every original
stage section. A family generating on the original closed stage generates
on the entire proper arithmetic family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonArithmeticStages
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] originalStageToCompatibleProj family exactVeroneseProj
variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : (exactVeroneseProj A π n h hne hgen).Modules) (hL : LocallyFreeRankOne L)
  (s : ∀ m, Γ(completeLineOnStage A π hne hgen n h L m, ⊤))
  (hs : ∀ a b (hab : a ≤ b),
    (completeLineStageTransitionIso A π hne hgen n h L (homOfLE hab)).hom.app ⊤
      (pullGlobal ((stageSystem A π n h).map (homOfLE hab)) _ (s b)) = s a)

/-- The unique actual section with the specified compatible original arithmetic restrictions. -/
def completeOriginalSectionLift : Γ(L, ⊤) := by
  have hs' := hs
  simp only [completeLineStageTransitionIso_eq_sealed] at hs'
  exact (completeLineOriginalSection_existsUnique A π hne hgen n h L hL s hs').exists.choose

/-- The chosen lift retains the original section at every arithmetic order. -/
theorem completeOriginalSectionLift_stage (m : ℕ) :
    pullGlobal (originalStageToCompatibleProj A π hne hgen n h m) L
      (completeOriginalSectionLift A π hne hgen n h L hL s hs) = s m := by
  unfold completeOriginalSectionLift
  have hs' := hs
  simp only [completeLineStageTransitionIso_eq_sealed] at hs'
  exact (completeLineOriginalSection_existsUnique A π hne hgen n h L hL s hs').exists.choose_spec m

/-- Its actual generator open has precisely the prescribed stage generator open. -/
theorem completeOriginalSectionLift_generatorOpen (m : ℕ) :
    originalStageToCompatibleProj A π hne hgen n h m ⁻¹ᵁ
        sectionGeneratorOpen L (completeOriginalSectionLift A π hne hgen n h L hL s hs) =
      sectionGeneratorOpen (completeLineOnStage A π hne hgen n h L m) (s m) := by
  rw [← sectionGeneratorOpen_pullGlobal hL, completeOriginalSectionLift_stage]
  rfl

/-- Generating on the original closed stage suffices for a reconstructed coordinate family. -/
theorem completeOriginalSectionLift_cover {ι : Type*}
    (t : ι → ∀ m, Γ(completeLineOnStage A π hne hgen n h L m, ⊤))
    (ht : ∀ i a b (hab : a ≤ b),
      (completeLineStageTransitionIso A π hne hgen n h L (homOfLE hab)).hom.app ⊤
        (pullGlobal ((stageSystem A π n h).map (homOfLE hab)) _ (t i b)) = t i a)
    (hcover : (⨆ i, sectionGeneratorOpen
      (completeLineOnStage A π hne hgen n h L 0) (t i 0)) = ⊤) :
    (⨆ i, sectionGeneratorOpen L
      (completeOriginalSectionLift A π hne hgen n h L hL (t i) (ht i))) = ⊤ := by
  apply completeOpenCover_of_originalZero A π hne hgen n h
  simpa only [completeOriginalSectionLift_generatorOpen] using hcover

end FLT.Mazur.PolygonArithmeticStages
