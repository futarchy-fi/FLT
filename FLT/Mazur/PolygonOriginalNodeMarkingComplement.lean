/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOriginalNodePoint
public import FLT.Mazur.SectionDivisors

/-!
# Original finite-stage nodes avoid every marking

The coordinate node lies on neither punctured branch, so the full cyclic
chart intersection relation separates it from every unit-one marking.
This supplies a canonical divisor frame near each original stage node.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K : Type) [Field K] (m n : ℕ) (h : 2 ≤ n)

/-- The original coordinate node is outside the outgoing punctured branch. -/
theorem stageNodePoint_not_leftBranch :
    stageNodePoint K m ∉ Set.range (leftBranchOpen (Ring K m) (parameter K m)) := by
  rw [leftBranchOpen_range]
  change ¬ leftCoordinate (parameter K m) ∉ coordinateIdeal (parameter K m)
  exact not_not.mpr (Ideal.subset_span (by simp))

/-- The original coordinate node is outside the incoming punctured branch. -/
theorem stageNodePoint_not_precedingBranch :
    stageNodePoint K m ∉ Set.range (precedingBranch (Ring K m) (parameter K m)) := by
  rw [precedingBranch_range, rightBranchOpen_range]
  change ¬ rightCoordinate (parameter K m) ∉ coordinateIdeal (parameter K m)
  exact not_not.mpr (Ideal.subset_span (by simp))

/-- No original finite-stage node is the image of any original unit-one marking. -/
theorem originalStageNode_not_marking_range (i j : Fin n) :
    originalStageNode K n h m i ∉ Set.range (marking K m n h j) := by
  rintro ⟨z, hz⟩
  have he : PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h i
      (stageNodePoint K m) =
        PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h j
          (markedSection (parameter K m) 1 z) := hz.symm
  by_cases hij : i = j
  · subst j
    have hp := (PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h i).isEmbedding.injective
      he
    exact stageNodePoint_not_leftBranch K m
      (hp.symm ▸ PolygonInfinitesimal.markedSection_mem_left (Ring K m) (parameter K m) 1 z)
  · rcases (PolygonInfinitesimal.charts_eq_iff (Ring K m) (parameter K m) n h hij _ _).mp he
      with ⟨w, _, hw, _⟩ | ⟨w, _, hw, _⟩
    · exact stageNodePoint_not_leftBranch K m ⟨w, hw⟩
    · exact stageNodePoint_not_precedingBranch K m ⟨w, hw⟩

/-- Each original node belongs to the complement of the same full stage marking ideal. -/
theorem originalStageNode_mem_marking_complement (i j : Fin n) :
    originalStageNode K n h m i ∈ (marking K m n h j).ker.support.compl := by
  change originalStageNode K n h m i ∉ (marking K m n h j).ker.support
  simpa only [← SetLike.mem_coe,
    support_section_ker (family K m n h).hom (marking K m n h j)
      (marking_base K m n h j)] using originalStageNode_not_marking_range K m n h i j

end FLT.Mazur.PolygonInfinitesimalStages
