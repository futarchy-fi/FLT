/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionRetainedMappedRatios
public import FLT.Mazur.PolygonCompleteCoefficientOpens

/-!
# Original boundary ratios beneath the complete Proj

The actual stage morphism evaluates each homogeneous coordinate ratio as
the ratio of its original boundary sections, on every generator subopen.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback SectionRetainedChartComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family boundaryStageRetainedIso
  SectionRetainedProjConstruction.toProj Proj.map compatibleEval exactVeroneseStep
  SectionRetainedChartComparison.toFunctions GradedProjMapChartSections.fractionMap
  Proj.awayToSection

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The actual complete coordinate ratio pulls back to its original boundary-section ratio. -/
theorem originalStage_coordinate_ratio (m d : ℕ) (hd : 0 < d)
    (s t : CompatibleVeroneseSections K n h (exactVeroneseStep K n h))
    (hs : s ∈ compatibleVeroneseGrade K n h (exactVeroneseStep K n h) d)
    (ht : t ∈ compatibleVeroneseGrade K n h (exactVeroneseStep K n h) d)
    (U : (family K m n h).left.Opens)
    (hU : U ≤ sectionGeneratorOpen
      (tensorPower (boundaryLine K m n h) (exactVeroneseStep K n h * d))
      (homogeneousBoundarySection K n h m d s hs)) :
    (originalStageToCompatibleProj K n h m).appLE
        (Proj.basicOpen (compatibleVeroneseGrade K n h (exactVeroneseStep K n h)) s)
        U (by rw [originalStageToCompatibleProj_basicOpen K n h m d hd s hs]; exact hU)
        (Proj.awayToSection (compatibleVeroneseGrade K n h (exactVeroneseStep K n h)) s
          (Away.mk (compatibleVeroneseGrade K n h (exactVeroneseStep K n h)) hs 1 t
            (by simpa only [one_smul] using ht))) =
      sectionRatioOn
        (tensorPower (boundaryLine K m n h) (exactVeroneseStep K n h * d))
        (homogeneousBoundarySection K n h m d s hs) U hU
        (homogeneousBoundarySection K n h m d t ht) := by
  let _ := boundaryExactRetainedGradedRing K n h m
  simp only [originalStageToCompatibleProj, boundaryStageRetainedIso_hom,
    boundaryStageToExactVeroneseProj, boundaryVeroneseProjToCompatible]
  exact SectionRetainedMappedRatios.coordinate_ratio
    (compatibleVeroneseGrade K n h (exactVeroneseStep K n h))
    (boundaryLine K m n h) (exactVeroneseStep K n h)
    (boundaryExactRetainedGenerated K n h m)
    (boundaryVeroneseEvaluation K n h (exactVeroneseStep K n h) m)
    (boundaryVeroneseEvaluation_irrelevant K n h m) d hd s t hs ht
    (homogeneousBoundarySection K n h m d s hs)
    (homogeneousBoundarySection K n h m d t ht)
    (homogeneousBoundarySection_insertion K n h m d s hs).symm
    (homogeneousBoundarySection_insertion K n h m d t ht).symm U hU _

end FLT.Mazur.PolygonInfinitesimalStages
