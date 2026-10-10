/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonStageRetainedCanonicalMap

/-!
# Homogeneous coordinates as original boundary sections

Evaluating a homogeneous compatible coordinate gives a section of the
original boundary tensor power. Its retained insertion is exactly the
original evaluation, without replacing the stage or its line bundle.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback SectionGradedSum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family compatibleEval

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (m d : ℕ) (s : CompatibleVeroneseSections K n h (exactVeroneseStep K n h))
  (hs : s ∈ compatibleVeroneseGrade K n h (exactVeroneseStep K n h) d)

/-- The original boundary section evaluated from a homogeneous compatible coordinate. -/
def homogeneousBoundarySection :
    Γ(tensorPower (boundaryLine K m n h) (exactVeroneseStep K n h * d), ⊤) :=
  Classical.choose ((boundaryVeroneseEvaluation K n h _ m).map_mem hs)

/-- Its full graded insertion is exactly the original evaluation. -/
theorem homogeneousBoundarySection_of :
    of (boundaryLine K m n h) ⊤ (exactVeroneseStep K n h * d)
        (homogeneousBoundarySection K n h m d s hs) =
      compatibleVeroneseEval K n h (exactVeroneseStep K n h) m s :=
  Classical.choose_spec ((boundaryVeroneseEvaluation K n h _ m).map_mem hs)

/-- Its retained insertion keeps the actual evaluation, including the subring codomain. -/
theorem homogeneousBoundarySection_insertion :
    SectionRetainedChartComparison.insertion (boundaryLine K m n h)
        (exactVeroneseStep K n h) d (homogeneousBoundarySection K n h m d s hs) =
      boundaryVeroneseEvaluation K n h (exactVeroneseStep K n h) m s :=
  Subtype.ext (homogeneousBoundarySection_of K n h m d s hs)

omit m in
/-- These actual sections are compatible with the original tensor-power stage maps. -/
theorem homogeneousBoundarySection_transition {a b : ℕ} (f : a ⟶ b) :
    SectionGradedIso.pieceMap (boundaryLineSystemIso K n h f)
        (exactVeroneseStep K n h * d) ⊤
        (SectionGradedPullback.pull ((stageSystem K n h).map f) (boundaryLine K b n h)
          (exactVeroneseStep K n h * d) ⊤ (homogeneousBoundarySection K n h b d s hs)) =
      homogeneousBoundarySection K n h a d s hs := by
  apply DirectSum.of_injective
  change of (boundaryLine K a n h) ⊤ _ _ = of (boundaryLine K a n h) ⊤ _ _
  rw [← boundarySectionsMap_of, homogeneousBoundarySection_of,
    homogeneousBoundarySection_of]
  exact DFunLike.congr_fun (compatibleVeroneseEval_transition K n h _ f) s

end FLT.Mazur.PolygonInfinitesimalStages
