/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointStagePoleSections
public import FLT.Mazur.ModuleSectionRatioOpenIso
public import FLT.Mazur.ModuleSectionRatioOpenNaturality
public import FLT.Mazur.LineBundleSectionOpenPullback

/-!
# Original cubic ratios on every full finite stage

The compared cubic sections cover the unchanged stage. Their ratios are
the actual restrictions of the chosen complete cubic ratios, with no
reduced-fiber replacement or new choice of normalized sections.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  family originalStageToCompatibleProj ModuleSheafTensor.tensor divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (i : Fin n)
local notation "f" => originalStageToCompatibleProj K n h m
local notation "L" => tensorPower (completePointLine K n h i) 3
local notation "M" => tensorPower (originalStageSinglePointLine K n h m i) 3
local notation "s" => completePointProjectiveSections K n h i
local notation "t" => completePointStageProjectiveSections K n h m i

/-- Each stage denominator generates on exactly the preimage of its original complete open. -/
theorem completePointStageProjectiveSections_generator (j : Fin 3) :
    sectionGeneratorOpen (M) (t j) = (f) ⁻¹ᵁ sectionGeneratorOpen (L) (s j) := by
  change sectionGeneratorOpen (M)
    ((completePointPowerOriginalStageIso K n h m i 3).hom.app ⊤
      (pullGlobal (f) (L) (s j))) = _
  rw [sectionGeneratorOpen_iso]
  exact sectionGeneratorOpen_pullGlobal
    ((completePointLine_locallyFreeRankOne K n h i).tensorPower 3) (f) (s j)

/-- The same three original cubic sections cover the full finite-stage scheme. -/
theorem completePointStageProjectiveSections_cover :
    ⨆ j, sectionGeneratorOpen (M) (t j) = ⊤ := by
  simp only [completePointStageProjectiveSections_generator,
    ← Scheme.Hom.preimage_iSup, completePointProjectiveSections_cover, Scheme.Hom.preimage_top]

/-- The stage Z denominator is exactly the complement of the unchanged stage marking. -/
theorem completePointStageProjectiveSections_Z_open :
    sectionGeneratorOpen (M) (t 2) = (marking K m n h i).ker.support.compl := by
  rw [completePointStageProjectiveSections_Z]
  erw [tensorPowerSection_generatorOpen
    (originalStageSingleMarking_relativeCartier K n h m i).1.divisorLineBundle_locallyFreeRankOne
    _ (by decide), divisorSection_generatorOpen]

/-- Local ratios after comparison are the actual complete ratios restricted to the same stage. -/
theorem completePointStageProjectiveSections_ratio (j k : Fin 3)
    (U : (exactVeroneseProj K n h).Opens)
    (V : (family K m n h).left.Opens) (hV : V ≤ (f) ⁻¹ᵁ U)
    (hU : U ≤ sectionGeneratorOpen (L) (s k)) :
    (f).appLE U V hV (sectionRatioOn (L) (s k) U hU (s j)) =
      sectionRatioOn (M) (t k) V
        (by rw [completePointStageProjectiveSections_generator]
            exact hV.trans ((f).preimage_mono hU)) (t j) := by
  have ht : V ≤ sectionGeneratorOpen ((pullback (f)).obj (L))
      (pullGlobal (f) (L) (s k)) := by
    rw [sectionGeneratorOpen_pullGlobal
      ((completePointLine_locallyFreeRankOne K n h i).tensorPower 3)]
    exact hV.trans ((f).preimage_mono hU)
  exact (sectionRatioOn_pullback (f) (L) U V hV (s k) (s j) hU ht).trans
    (sectionRatioOn_iso (completePointPowerOriginalStageIso K n h m i 3)
      (pullGlobal (f) (L) (s k)) (pullGlobal (f) (L) (s j)) V ht).symm

end FLT.Mazur.PolygonInfinitesimalStages
