/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonStageVeroneseGrading
public import FLT.Mazur.RingEquivGrading

/-!
# The original grading on the actual adic quotient

Transport the independently constructed stage grading through the existing adic
reduction. Each quotient degree is exactly the image of the original compatible
degree; no new section representatives or multiplication are substituted.
-/

@[expose] public noncomputable section

open scoped DirectSum

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval boundaryLine family

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The internal homogeneous groups on the actual parameter-power quotient. -/
def exactVeroneseQuotientGrade (m d : ℕ) : AddSubgroup
    (CompatibleVeroneseSections K n h (exactVeroneseStep K n h) ⧸
      compatibleVeroneseParameterIdeal K n h (exactVeroneseStep K n h) ^ (m + 1)) :=
  RingEquivGrading.grade (boundaryVeroneseGrade K n h (exactVeroneseStep K n h) m)
    (exactVeroneseAdicReduction K n h m) d

/-- The actual adic quotient is internally graded by its retained original degrees. -/
instance exactVeroneseQuotientGradedRing (m : ℕ) :
    GradedRing (exactVeroneseQuotientGrade K n h m) :=
  RingEquivGrading.gradedRing _ _

/-- Reduction preserves and reflects every original retained homogeneous degree. -/
theorem exactVeroneseAdicReduction_mem_iff (m d : ℕ) (s) :
    exactVeroneseAdicReduction K n h m s ∈
        boundaryVeroneseGrade K n h (exactVeroneseStep K n h) m d ↔
      s ∈ exactVeroneseQuotientGrade K n h m d := Iff.rfl

/-- The adic reduction keeps the original evaluation of every homogeneous insertion. -/
theorem exactVeroneseAdicReduction_of (m d : ℕ)
    (s : compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d) :
    exactVeroneseAdicReduction K n h m (Ideal.Quotient.mk _ (DirectSum.of _ d s)) =
      boundaryVeroneseEvaluation K n h (exactVeroneseStep K n h) m
        (DirectSum.of _ d s) := rfl

/-- Membership in a quotient degree means having an original homogeneous representative. -/
theorem exactVeroneseQuotientGrade_mem_iff (m d : ℕ) (s) :
    s ∈ exactVeroneseQuotientGrade K n h m d ↔
      ∃ t : compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d,
        Ideal.Quotient.mk _ (DirectSum.of _ d t) = s := by
  constructor
  · intro hs
    obtain ⟨t, ht⟩ := boundaryVeroneseEvaluation_homogeneous_surjective K n h m d
      ⟨exactVeroneseAdicReduction K n h m s, hs⟩
    refine ⟨t, (exactVeroneseAdicReduction K n h m).injective ?_⟩
    rw [exactVeroneseAdicReduction_of]
    exact ht
  · rintro ⟨t, rfl⟩
    change boundaryVeroneseEvaluation K n h (exactVeroneseStep K n h) m
      (DirectSum.of _ d t) ∈ boundaryVeroneseGrade K n h (exactVeroneseStep K n h) m d
    exact (boundaryVeroneseEvaluation K n h _ m).map_mem ⟨t, rfl⟩

/-- Quotient degrees are precisely the images of the actual compatible internal degrees. -/
theorem exactVeroneseQuotientGrade_eq_map (m d : ℕ) :
    exactVeroneseQuotientGrade K n h m d =
      (compatibleVeroneseGrade K n h (exactVeroneseStep K n h) d).toAddSubgroup.map
        (Ideal.Quotient.mk
          (compatibleVeroneseParameterIdeal K n h (exactVeroneseStep K n h) ^
            (m + 1))).toAddMonoidHom := by
  ext s
  rw [exactVeroneseQuotientGrade_mem_iff]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨DirectSum.of _ d t, ⟨t, rfl⟩, rfl⟩
  · rintro ⟨t, ⟨u, rfl⟩, ht⟩
    exact ⟨u, ht⟩

/-- The original quotient map preserves the actual internal grading. -/
def exactVeroneseGradedQuotient (m : ℕ) :
    compatibleVeroneseGrade K n h (exactVeroneseStep K n h) →+*ᵍ
      exactVeroneseQuotientGrade K n h m where
  __ := Ideal.Quotient.mk _
  map_mem := by
    rintro d s ⟨t, rfl⟩
    exact (exactVeroneseQuotientGrade_mem_iff K n h m d _).mpr ⟨t, rfl⟩

end FLT.Mazur.PolygonInfinitesimalStages
