/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingNodeBasicOpen
public import FLT.Mazur.PolygonCompletePointStageNodeFunctions

/-!
# A specified basic neighborhood for the actual stage pole functions

On every full arithmetic stage, D((1-x)(1-y)) contains the coordinate node
and avoids every marking in the glued polygon, including both two-gon overlaps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (m n : ℕ) (h : 2 ≤ n)

/-- The explicit denominator is invertible at the original coordinate node. -/
theorem stageNodePoint_mem_nodeMarkingBasicOpen :
    stageNodePoint K m ∈ nodeMarkingBasicOpen (parameter K m) := by
  change (1 - leftCoordinate (parameter K m)) *
    (1 - rightCoordinate (parameter K m)) ∉ (stageNodePoint K m).asIdeal
  rw [(stageNodePoint K m).isPrime.mul_mem_iff_mem_or_mem, not_or]
  constructor
  all_goals
    intro hmem
    apply (stageNodePoint K m).isPrime.ne_top
    apply Ideal.eq_top_of_isUnit_mem _ _ isUnit_one
    have hx : leftCoordinate (parameter K m) ∈ (stageNodePoint K m).asIdeal :=
      Ideal.subset_span (by simp)
    have hy : rightCoordinate (parameter K m) ∈ (stageNodePoint K m).asIdeal :=
      Ideal.subset_span (by simp)
    first
    | simpa only [sub_add_cancel] using (stageNodePoint K m).asIdeal.add_mem hmem hx
    | simpa only [sub_add_cancel] using (stageNodePoint K m).asIdeal.add_mem hmem hy

/-- Every marking is excluded from the image of the explicit node neighborhood. -/
theorem nodeMarkingBasicOpen_not_marking_range (i j : Fin n)
    (x : PolygonSmoothing.chart (Ring K m) (parameter K m))
    (hx : x ∈ nodeMarkingBasicOpen (parameter K m)) :
    PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h j x ∉
      Set.range (marking K m n h i) := by
  rintro ⟨z, hz⟩
  have he : PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h j x =
      PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h i
        (markedSection (parameter K m) 1 z) := hz.symm
  by_cases hji : j = i
  · subst j
    have hp := (PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h i).isEmbedding.injective
      he
    exact markedSection_not_nodeMarkingBasicOpen (parameter K m) z (hp ▸ hx)
  · rcases (PolygonInfinitesimal.charts_eq_iff (Ring K m) (parameter K m) n h hji _ _).mp he
      with ⟨w, _, _, hw⟩ | ⟨w, _, hw, hw'⟩
    · exact PolygonInfinitesimal.markedSection_not_mem_preceding
        (Ring K m) (parameter K m) 1 z ⟨w, hw⟩
    · have hew : w = markedTorusSection (1 : (Ring K m)ˣ) z := by
        apply (leftBranchOpen (Ring K m) (parameter K m)).isEmbedding.injective
        exact hw'.trans
          (congrArg (fun f ↦ f z) (markedTorusSection_left (parameter K m) 1)).symm
      rw [hew] at hw
      exact preceding_markedSection_not_nodeMarkingBasicOpen (parameter K m) z (hw ▸ hx)

/-- The explicit original basic open supports the same retained complete pole functions. -/
theorem nodeMarkingBasicOpen_le_completePointStageNodeOpen (i j : Fin n) :
    nodeMarkingBasicOpen (parameter K m) ≤ completePointStageNodeOpen K n h m i j := by
  intro x hx
  change PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h j x ∉
    (marking K m n h i).ker.support
  simpa only [← SetLike.mem_coe,
    FCurve.support_section_ker (family K m n h).hom (marking K m n h i)
      (marking_base K m n h i)] using
    nodeMarkingBasicOpen_not_marking_range K m n h i j x hx

end FLT.Mazur.PolygonInfinitesimalStages
