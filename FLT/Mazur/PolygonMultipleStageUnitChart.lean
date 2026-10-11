/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonPositiveRetainedStage
public import FLT.Mazur.SectionRetainedHomogeneousChart
public import FLT.Mazur.GradedProjUnitChartMap

/-!
# Original stage maps on compatible unit coordinates

The original stage recovery followed by compatible evaluation is computed on
any positive homogeneous compatible section that is a unit in line coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] compatibleEval boundaryLine family
  SectionRetainedProjConstruction.toProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (q : ℕ) [NeZero q] (hq : exactVeroneseStep K n h ∣ q)

/-- Original retained stage rings carry their positive-step grading. -/
local instance unitStageGradedRing (m : ℕ) : GradedRing (boundaryVeroneseGrade K n h q m) :=
  boundaryVeroneseGradedRing K n h q (NeZero.pos q) m

/-- The stage morphism keeps the original line-coordinate evaluation on every compatible unit. -/
@[reassoc]
theorem originalStageToMultipleProj_unit (m : ℕ) {Y : Scheme}
    (p : Y ⟶ (family K m n h).left)
    (e : (pullback p).obj (boundaryLine K m n h) ≅ structureModule Y)
    {d : ℕ} (s : CompatibleVeroneseSections K n h q)
    (hs : s ∈ compatibleVeroneseGrade K n h q d) (hd : 0 < d)
    (hu : IsUnit (SectionGradedProjChart.ringHom p (boundaryLine K m n h) e
      (compatibleVeroneseEval K n h q m s))) :
    p ≫ originalStageToMultipleProj K n h q hq m =
      GradedProjUnitChart.toProj (compatibleVeroneseGrade K n h q)
        ((SectionGradedProjChart.ringHom p (boundaryLine K m n h) e).comp
          (compatibleVeroneseEval K n h q m)) s hu hs hd := by
  let _ : GradedRing (RetainedSubringGrading.grade
      (SectionGradedSum.grade (boundaryLine K m n h) ⊤) q) :=
    boundaryVeroneseGradedRing K n h q (NeZero.pos q) m
  rw [originalStageToMultipleProj, ← Category.assoc, boundaryPositiveRetainedIso_hom]
  rw [SectionRetainedHomogeneousChart.toProj_comp _ _ _ p e
    (boundaryVeroneseEvaluation K n h q m s)
    ((boundaryVeroneseEvaluation K n h q m).map_mem hs) hd hu]
  exact GradedProjUnitChartMap.toProj_map _ _ (boundaryVeroneseEvaluation K n h q m)
    (SectionRetainedProjChart.ringHom p (boundaryLine K m n h) e q)
    (multipleVeroneseEvaluation_irrelevant K n h q hq m) s hs hd hu

end FLT.Mazur.PolygonInfinitesimalStages
