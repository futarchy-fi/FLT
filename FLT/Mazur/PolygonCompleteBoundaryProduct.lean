/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteMarkingLineTransition
public import FLT.Mazur.PolygonInfinitesimalSpecialDivisor

/-!
# The complete product line on the original closed polygon

The original closed polygon maps through the zeroth stage into the complete
smoothing. Its whole product ideal and canonical positive-line section agree
with the original all-one boundary product, without choosing a new polygon.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj completeMarkingDivisor
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original closed polygon's map into the actual complete smoothing. -/
def completeBoundaryInclusion :
    PolygonCyclicAtlas.scheme K n h ⟶ exactVeroneseProj K n h :=
  specialFiberInclusion K 0 n h ≫ originalStageToCompatibleProj K n h 0

/-- Restriction is the entire original unit-one boundary product. -/
theorem completeMarkingDivisor_boundary :
    (completeMarkingDivisor K n h).comap (completeBoundaryInclusion K n h) =
      PolygonBoundaryDivisor.ideal K n (PolygonCyclicAtlas.normalization K n h)
        (fun _ ↦ 1) := by
  rw [completeBoundaryInclusion, Scheme.IdealSheafData.comap_comp,
    completeMarkingDivisor_originalBoundary]
  exact boundaryIdeal_specialFiberInclusion K 0 n h

/-- The smoothing's positive line recovers the original whole boundary product line. -/
irreducible_def completeBoundaryProductLineIso :
    (Scheme.Modules.pullback (completeBoundaryInclusion K n h)).obj
      (completeMarkingLine K n h) ≅
        divisorLineBundle
          (PolygonBoundaryDivisor.ideal K n (PolygonCyclicAtlas.normalization K n h)
            (fun _ ↦ 1)) (specialBoundary_cartier K n h).1 := by
  let hs := (completeMarkingDivisor_relativeCartier K n h).1
  let ht := (specialBoundary_cartier K n h).1
  let he := completeMarkingDivisor_boundary K n h
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  exact divisorLinePullbackIsoOfEq _ hs ht he

/-- The boundary comparison retains the canonical section, with no unit rescaling. -/
theorem completeBoundaryProductLineIso_section :
    DivisorLineSectionCompatible (completeBoundaryInclusion K n h)
      (completeMarkingDivisor_relativeCartier K n h).1 (specialBoundary_cartier K n h).1
      (completeBoundaryProductLineIso K n h) := by
  let hs := (completeMarkingDivisor_relativeCartier K n h).1
  let ht := (specialBoundary_cartier K n h).1
  let he := completeMarkingDivisor_boundary K n h
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  rw [completeBoundaryProductLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- Direct restriction agrees with the original zeroth-stage route. -/
theorem completeBoundaryProductLineIso_stage_triangle :
    LinePullbackTriangle (specialFiberInclusion K 0 n h)
      (originalStageToCompatibleProj K n h 0) (completeBoundaryInclusion K n h) rfl
      (completeMarkingLineStageIso K n h 0) (boundaryLineSpecialFiberIso K 0 n h)
      (completeBoundaryProductLineIso K n h) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (divisorLinePullbackIsoOfEq_compatible _ _ _ _)
    (divisorLinePullbackIsoOfEq_compatible _ _ _ _)
    (completeBoundaryProductLineIso_section K n h)

end FLT.Mazur.PolygonInfinitesimalStages
