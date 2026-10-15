/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticAdicReduction
public import FLT.Mazur.PolygonArithmeticVeroneseGrading
public import FLT.Mazur.RetainedSubringGrading
public import Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# The original retained grading on each polygon stage

The independently defined stage subring is internally graded by its original
retained section degrees. Actual compatible evaluation preserves these degrees
and is surjective on each of them for the previously constructed exact step.
-/

@[expose] public noncomputable section

open scoped DirectSum

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval boundaryLine family

variable (A : Type) [CommRing A] (π : A) (n : ℕ) (h : 2 ≤ n)

/-- A retained stage degree consists of the original homogeneous sections in that degree. -/
def boundaryVeroneseGrade (q m d : ℕ) : AddSubgroup (boundaryVeroneseRing A π n h q m) :=
  RetainedSubringGrading.grade (SectionGradedSum.grade (boundaryLine A π m n h) ⊤) q d

/-- Original stage sections internally grade the retained ring for a positive step. -/
@[instance_reducible]
def boundaryVeroneseGradedRing (q : ℕ) (hq : 0 < q) (m : ℕ) :
    GradedRing (boundaryVeroneseGrade A π n h q m) :=
  RetainedSubringGrading.gradedRing (SectionGradedSum.grade (boundaryLine A π m n h) ⊤) q hq

/-- The actual evaluation, with its proved codomain restricted to the original retained ring. -/
def boundaryVeroneseEvaluation (q m : ℕ) :
    compatibleVeroneseGrade A π n h q →+*ᵍ boundaryVeroneseGrade A π n h q m where
  __ := (compatibleVeroneseEval A π n h q m).codRestrict _
    (compatibleVeroneseEval_mem A π n h q m)
  map_mem := by
    rintro d s ⟨t, rfl⟩
    change compatibleVeroneseEval A π n h q m (DirectSum.of _ d t) ∈
      SectionGradedSum.grade (boundaryLine A π m n h) ⊤ (q * d)
    rw [compatibleVeroneseEval_of]
    exact t.property m

/-- Homogeneous evaluation is the original stage projection on each original insertion. -/
theorem boundaryVeroneseEvaluation_of (q m d : ℕ) (s : compatibleVeroneseDegree A π n h q d) :
    (boundaryVeroneseEvaluation A π n h q m (DirectSum.of _ d s)).val =
      compatibleEval A π n h m s :=
  compatibleVeroneseEval_of A π n h q m d s

variable [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π) [NeZero n]

/-- The exact step provides the original grading on every truncated stage ring. -/
instance boundaryExactVeroneseGradedRing (m : ℕ) :
    GradedRing (boundaryVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h) m) :=
  boundaryVeroneseGradedRing A π n h _ (exactVeroneseStep_pos A π hne hgen n h) m

/-- Every retained homogeneous stage section has an original compatible homogeneous lift. -/
theorem boundaryVeroneseEvaluation_homogeneous_surjective (m d : ℕ)
    (s : boundaryVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h) m d) :
    ∃ t : compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d,
      boundaryVeroneseEvaluation A π n h (exactVeroneseStep A π hne hgen n h) m
        (DirectSum.of _ d t) = s := by
  obtain ⟨t, ht⟩ := exactVeroneseDegree_surjective A π hne hgen n h d m ⟨s.val.val, s.property⟩
  refine ⟨t, Subtype.ext ?_⟩
  rw [boundaryVeroneseEvaluation_of]
  exact congrArg Subtype.val ht

end FLT.Mazur.PolygonArithmeticStages
