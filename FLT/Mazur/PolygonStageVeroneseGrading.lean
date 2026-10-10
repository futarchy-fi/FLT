/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonVeroneseAdicReduction
public import FLT.Mazur.PolygonVeroneseGrading
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

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval boundaryLine family

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n)

/-- A retained stage degree consists of the original homogeneous sections in that degree. -/
def boundaryVeroneseGrade (q m d : ℕ) : AddSubgroup (boundaryVeroneseRing K n h q m) :=
  RetainedSubringGrading.grade (SectionGradedSum.grade (boundaryLine K m n h) ⊤) q d

/-- Original stage sections internally grade the retained ring for a positive step. -/
@[instance_reducible]
def boundaryVeroneseGradedRing (q : ℕ) (hq : 0 < q) (m : ℕ) :
    GradedRing (boundaryVeroneseGrade K n h q m) :=
  RetainedSubringGrading.gradedRing (SectionGradedSum.grade (boundaryLine K m n h) ⊤) q hq

/-- The actual evaluation, with its proved codomain restricted to the original retained ring. -/
def boundaryVeroneseEvaluation (q m : ℕ) :
    compatibleVeroneseGrade K n h q →+*ᵍ boundaryVeroneseGrade K n h q m where
  __ := (compatibleVeroneseEval K n h q m).codRestrict _
    (compatibleVeroneseEval_mem K n h q m)
  map_mem := by
    rintro d s ⟨t, rfl⟩
    change compatibleVeroneseEval K n h q m (DirectSum.of _ d t) ∈
      SectionGradedSum.grade (boundaryLine K m n h) ⊤ (q * d)
    rw [compatibleVeroneseEval_of]
    exact t.property m

/-- Homogeneous evaluation is the original stage projection on each original insertion. -/
theorem boundaryVeroneseEvaluation_of (q m d : ℕ) (s : compatibleVeroneseDegree K n h q d) :
    (boundaryVeroneseEvaluation K n h q m (DirectSum.of _ d s)).val =
      compatibleEval K n h m s :=
  compatibleVeroneseEval_of K n h q m d s

variable [NeZero n]

/-- The exact step provides the original grading on every truncated stage ring. -/
instance boundaryExactVeroneseGradedRing (m : ℕ) :
    GradedRing (boundaryVeroneseGrade K n h (exactVeroneseStep K n h) m) :=
  boundaryVeroneseGradedRing K n h _ (exactVeroneseStep_pos K n h) m

/-- Every retained homogeneous stage section has an original compatible homogeneous lift. -/
theorem boundaryVeroneseEvaluation_homogeneous_surjective (m d : ℕ)
    (s : boundaryVeroneseGrade K n h (exactVeroneseStep K n h) m d) :
    ∃ t : compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d,
      boundaryVeroneseEvaluation K n h (exactVeroneseStep K n h) m
        (DirectSum.of _ d t) = s := by
  obtain ⟨t, ht⟩ := exactVeroneseDegree_surjective K n h d m ⟨s.val.val, s.property⟩
  refine ⟨t, Subtype.ext ?_⟩
  rw [boundaryVeroneseEvaluation_of]
  exact congrArg Subtype.val ht

end FLT.Mazur.PolygonInfinitesimalStages
