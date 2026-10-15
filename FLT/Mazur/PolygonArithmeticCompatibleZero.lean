/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticDegreeExactness
public import FLT.Mazur.PolygonArithmeticZeroTower

/-!
# Exact reduction in the retained compatible degree zero

Every stage-zero-degree section lifts from an original integral-base
coefficient. Compatible division identifies the actual evaluation kernel
with the corresponding parameter power, just as in positive degrees.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval boundaryLine family boundaryIntegralScalars

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  (n : ℕ) (h : 2 ≤ n) [NeZero n]

include hne hgen in
/-- Degree-zero evaluation lifts every stage section from an original integral-base coefficient. -/
theorem compatibleDegreeEval_zero_surjective (m : ℕ) :
    Function.Surjective (compatibleDegreeEval A π n h m 0) := by
  rintro ⟨s, ⟨u, rfl⟩⟩
  obtain ⟨r, hr⟩ := stageScalars_surjective A π n h hgen hne m u
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective r
  let t : compatibleSectionDegree A π n h 0 :=
    ⟨f • (1 : CompatibleSections A π n h),
      isCompatibleDegree_smul A π n h 0 f (compatibleSectionDegree_one A π n h)⟩
  refine ⟨t, Subtype.ext ?_⟩
  change compatibleEval A π n h m (f • (1 : CompatibleSections A π n h)) =
    SectionGradedSum.of (boundaryLine A π m n h) ⊤ 0 u
  rw [Algebra.smul_def, mul_one, compatibleEval_algebraMap, boundaryIntegralScalars_stage, hf]
  exact congrArg (SectionGradedSum.of (boundaryLine A π m n h) ⊤ 0) hr

include hne hgen in
/-- The retained degree-zero evaluation kernel is exactly its original parameter-power image. -/
theorem compatibleDegreeEval_zero_kernel (m : ℕ)
    (s : compatibleSectionDegree A π n h 0) :
    compatibleDegreeEval A π n h m 0 s = 0 ↔
      ∃ t : compatibleSectionDegree A π n h 0,
        π ^ (m + 1) • t = s := by
  constructor
  · intro hz
    obtain ⟨t, ht, he⟩ := boundaryIntegralDegree_zero_powerDivision A π hne hgen n h m
      (fun a ↦ compatibleDegreeEval A π n h a 0 s)
      (fun a ↦ compatibleDegreeEval_adjacent A π n h a 0 s) hz
    refine ⟨compatibleDegreeOfAdjacent A π n h 0 t ht, ?_⟩
    apply Subtype.ext
    apply compatibleEval_ext A π n h
    intro a
    rw [compatibleDegree_eval_smul, compatibleDegreeOfAdjacent_eval]
    exact (boundaryIntegralDegree_smul_val A π n h a 0 _ (t a)).symm.trans
      (congrArg Subtype.val (he a))
  · rintro ⟨t, rfl⟩
    exact compatibleDegreeEval_parameterPower A π n h m 0 t

end FLT.Mazur.PolygonArithmeticStages
