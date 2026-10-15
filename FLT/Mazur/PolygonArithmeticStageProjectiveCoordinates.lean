/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticProjectiveReconstruction
public import FLT.Mazur.ModuleSectionProjectiveNaturality

/-!
# The original arithmetic projective morphism at every finite order

The algebraized projective morphism restricts to the morphism of the supplied
stage sections, with its original arithmetic coefficient map. This identifies
the full scheme morphisms, not just their inverse-image chart opens.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonArithmeticStages
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] originalStageToCompatibleProj family
  exactVeroneseProj exactVeroneseProjToBase completeOriginalSectionLift
variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : (exactVeroneseProj A π n h hne hgen).Modules) (hL : LocallyFreeRankOne L)
  (d : ℕ) (s : Fin (d + 1) → ∀ m, Γ(completeLineOnStage A π hne hgen n h L m, ⊤))
  (hs : ∀ i a b (hab : a ≤ b),
    (completeLineStageTransitionIso A π hne hgen n h L (homOfLE hab)).hom.app ⊤
      (pullGlobal ((stageSystem A π n h).map (homOfLE hab)) _ (s i b)) = s i a)
  (hcover : (⨆ i, sectionGeneratorOpen
    (completeLineOnStage A π hne hgen n h L 0) (s i 0)) = ⊤)

include hL hs hcover in
/-- The specified coordinate sections generate at every original arithmetic order. -/
theorem completeOriginalStageSections_cover (m : ℕ) :
    (⨆ i, sectionGeneratorOpen (completeLineOnStage A π hne hgen n h L m) (s i m)) = ⊤ := by
  have he := sectionGeneratorCover_pullback
    (originalStageToCompatibleProj A π hne hgen n h m) L hL d
    (fun i ↦ completeOriginalSectionLift A π hne hgen n h L hL (s i) (hs i))
    (completeOriginalSectionLift_cover A π hne hgen n h L hL s hs hcover)
  simpa only [completeOriginalSectionLift_stage, completeLineOnStage] using he

/-- The full original-stage projective map uses the original integral coefficient morphism. -/
@[reassoc] theorem completeOriginalProjectiveMap_stage (m : ℕ) :
    originalStageToCompatibleProj A π hne hgen n h m ≫
        completeOriginalProjectiveMap A π hne hgen n h L hL d s hs hcover =
      sectionProjectiveMorphism (completeLineOnStage A π hne hgen n h L m) d
        (fun i ↦ s i m) (completeOriginalStageSections_cover A π hne hgen n h L hL d s hs
          hcover m) (((family A π m n h).hom ≫ baseToIntegral A π m).appTop.hom.comp
            (Scheme.ΓSpecIso (.of A)).inv.hom) := by
  rw [completeOriginalProjectiveMap, sectionProjectiveMorphism_pullback _ L hL]
  have he : (originalStageToCompatibleProj A π hne hgen n h m).appTop.hom.comp
      ((exactVeroneseProjToBase A π n h hne hgen).appTop.hom.comp
        (Scheme.ΓSpecIso (.of A)).inv.hom) =
      ((family A π m n h).hom ≫ baseToIntegral A π m).appTop.hom.comp
        (Scheme.ΓSpecIso (.of A)).inv.hom := by
    rw [← RingHom.comp_assoc]
    change (originalStageToCompatibleProj A π hne hgen n h m ≫
      exactVeroneseProjToBase A π n h hne hgen).appTop.hom.comp _ = _
    rw [originalStageToCompatibleProj_toBase]
  simp only [completeOriginalSectionLift_stage, he, completeLineOnStage]

end FLT.Mazur.PolygonArithmeticStages
