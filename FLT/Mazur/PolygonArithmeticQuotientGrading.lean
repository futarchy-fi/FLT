/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticStageGrading
public import FLT.Mazur.RingEquivGrading

/-!
# The original grading on the actual adic quotient

Transport the independently constructed stage grading through the existing adic
reduction. Each quotient degree is exactly the image of the original compatible
degree; no new section representatives or multiplication are substituted.
-/

@[expose] public noncomputable section

open scoped DirectSum

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval boundaryLine family

variable (A : Type) [CommRing A] (π : A) (n : ℕ) (h : 2 ≤ n)
  [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π) [NeZero n]

/-- The internal homogeneous groups on the actual parameter-power quotient. -/
def exactVeroneseQuotientGrade (m d : ℕ) : AddSubgroup
    (CompatibleVeroneseSections A π n h (exactVeroneseStep A π hne hgen n h) ⧸
      compatibleVeroneseParameterIdeal A π n h (exactVeroneseStep A π hne hgen n h) ^ (m + 1)) :=
  RingEquivGrading.grade (boundaryVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h) m)
    (exactVeroneseAdicReduction A π n h hne hgen m) d

/-- The actual adic quotient is internally graded by its retained original degrees. -/
instance exactVeroneseQuotientGradedRing (m : ℕ) :
    GradedRing (exactVeroneseQuotientGrade A π n h hne hgen m) :=
  RingEquivGrading.gradedRing _ _

/-- Reduction preserves and reflects every original retained homogeneous degree. -/
theorem exactVeroneseAdicReduction_mem_iff (m d : ℕ) (s) :
    exactVeroneseAdicReduction A π n h hne hgen m s ∈
        boundaryVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h) m d ↔
      s ∈ exactVeroneseQuotientGrade A π n h hne hgen m d := Iff.rfl

/-- The adic reduction keeps the original evaluation of every homogeneous insertion. -/
theorem exactVeroneseAdicReduction_of (m d : ℕ)
    (s : compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d) :
    exactVeroneseAdicReduction A π n h hne hgen m (Ideal.Quotient.mk _ (DirectSum.of _ d s)) =
      boundaryVeroneseEvaluation A π n h (exactVeroneseStep A π hne hgen n h) m
        (DirectSum.of _ d s) := rfl

/-- Membership in a quotient degree means having an original homogeneous representative. -/
theorem exactVeroneseQuotientGrade_mem_iff (m d : ℕ) (s) :
    s ∈ exactVeroneseQuotientGrade A π n h hne hgen m d ↔
      ∃ t : compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d,
        Ideal.Quotient.mk _ (DirectSum.of _ d t) = s := by
  constructor
  · intro hs
    obtain ⟨t, ht⟩ := boundaryVeroneseEvaluation_homogeneous_surjective A π n h hne hgen m d
      ⟨exactVeroneseAdicReduction A π n h hne hgen m s, hs⟩
    refine ⟨t, (exactVeroneseAdicReduction A π n h hne hgen m).injective ?_⟩
    rw [exactVeroneseAdicReduction_of]
    exact ht
  · rintro ⟨t, rfl⟩
    change boundaryVeroneseEvaluation A π n h (exactVeroneseStep A π hne hgen n h) m
      (DirectSum.of _ d t) ∈ boundaryVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h) m d
    exact (boundaryVeroneseEvaluation A π n h _ m).map_mem ⟨t, rfl⟩

/-- Quotient degrees are precisely the images of the actual compatible internal degrees. -/
theorem exactVeroneseQuotientGrade_eq_map (m d : ℕ) :
    exactVeroneseQuotientGrade A π n h hne hgen m d =
      (compatibleVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h) d).toAddSubgroup.map
        (Ideal.Quotient.mk
          (compatibleVeroneseParameterIdeal A π n h (exactVeroneseStep A π hne hgen n h) ^
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
    compatibleVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h) →+*ᵍ
      exactVeroneseQuotientGrade A π n h hne hgen m where
  __ := Ideal.Quotient.mk _
  map_mem := by
    rintro d s ⟨t, rfl⟩
    exact (exactVeroneseQuotientGrade_mem_iff A π n h hne hgen m d _).mpr ⟨t, rfl⟩

end FLT.Mazur.PolygonArithmeticStages
