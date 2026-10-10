/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompatibleDegreeExactness
public import FLT.Mazur.PolygonDegreeZeroTower

/-!
# Exact reduction in the retained compatible degree zero

Every stage-zero-degree section lifts from an original complete-base
coefficient. Compatible division identifies the actual evaluation kernel
with the corresponding parameter power, just as in positive degrees.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval boundaryLine family boundarySeriesScalars

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Degree-zero evaluation lifts every stage section from an original complete-base coefficient. -/
theorem compatibleDegreeEval_zero_surjective (m : ℕ) :
    Function.Surjective (compatibleDegreeEval K n h m 0) := by
  rintro ⟨s, ⟨u, rfl⟩⟩
  obtain ⟨r, hr⟩ := stageScalars_surjective K n h m u
  obtain ⟨f, hf⟩ := seriesToStage_surjective K m r
  let t : compatibleSectionDegree K n h 0 :=
    ⟨f • (1 : CompatibleSections K n h),
      isCompatibleDegree_smul K n h 0 f (compatibleSectionDegree_one K n h)⟩
  refine ⟨t, Subtype.ext ?_⟩
  change compatibleEval K n h m (f • (1 : CompatibleSections K n h)) =
    SectionGradedSum.of (boundaryLine K m n h) ⊤ 0 u
  rw [Algebra.smul_def, mul_one, compatibleEval_algebraMap, boundarySeriesScalars_stage, hf]
  exact congrArg (SectionGradedSum.of (boundaryLine K m n h) ⊤ 0) hr

/-- The retained degree-zero evaluation kernel is exactly its original parameter-power image. -/
theorem compatibleDegreeEval_zero_kernel (m : ℕ)
    (s : compatibleSectionDegree K n h 0) :
    compatibleDegreeEval K n h m 0 s = 0 ↔
      ∃ t : compatibleSectionDegree K n h 0,
        (PowerSeries.X : PowerSeries K) ^ (m + 1) • t = s := by
  constructor
  · intro hz
    obtain ⟨t, ht, he⟩ := boundarySeriesDegree_zero_powerDivision K n h m
      (fun a ↦ compatibleDegreeEval K n h a 0 s)
      (fun a ↦ compatibleDegreeEval_adjacent K n h a 0 s) hz
    refine ⟨compatibleDegreeOfAdjacent K n h 0 t ht, ?_⟩
    apply Subtype.ext
    apply compatibleEval_ext K n h
    intro a
    rw [compatibleDegree_eval_smul, compatibleDegreeOfAdjacent_eval]
    exact (boundarySeriesDegree_smul_val K n h a 0 _ (t a)).symm.trans
      (congrArg Subtype.val (he a))
  · rintro ⟨t, rfl⟩
    exact compatibleDegreeEval_parameterPower K n h m 0 t

end FLT.Mazur.PolygonInfinitesimalStages
