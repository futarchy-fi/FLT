/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticStageGrading
public import FLT.Mazur.GradedQuotientTensorComparison

/-!
# Original stage reduction as graded coefficient base change

The actual parameter-power quotient is the tensor product with the truncated
coefficient ring. Its existing evaluation equivalence preserves and reflects
the independently constructed original stage degrees.
-/

@[expose] public noncomputable section

open scoped TensorProduct DirectSum

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval boundaryLine family

variable (A : Type) [CommRing A] (π : A) (n : ℕ) (h : 2 ≤ n)
  [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π) [NeZero n]

/-- The original coefficient ideal power maps to the actual compatible parameter ideal power. -/
theorem exactVeroneseParameter_map (m : ℕ) :
    (ideal A π ^ (m + 1)).map
        (algebraMap (A)
          (CompatibleVeroneseSections A π n h (exactVeroneseStep A π hne hgen n h))) =
      compatibleVeroneseParameterIdeal A π n h (exactVeroneseStep A π hne hgen n h) ^ (m + 1) := by
  rw [Ideal.map_pow, ideal, compatibleVeroneseParameterIdeal,
    Ideal.map_span, Set.image_singleton]

/-- The actual stage evaluation is an equivalence from coefficient scalar extension. -/
def exactVeroneseTensorReduction (m : ℕ) :
    (A ⧸ ideal A π ^ (m + 1)) ⊗[A]
        CompatibleVeroneseSections A π n h (exactVeroneseStep A π hne hgen n h) ≃+*
      boundaryVeroneseRing A π n h (exactVeroneseStep A π hne hgen n h) m :=
  ((GradedQuotientTensorComparison.equiv (ideal A π ^ (m + 1))).trans
    (Ideal.quotEquivOfEq (exactVeroneseParameter_map A π n h hne hgen m))).trans
      (exactVeroneseAdicReduction A π n h hne hgen m)

/-- Scalar extension retains every original compatible evaluation. -/
theorem exactVeroneseTensorReduction_one_tmul (m : ℕ)
    (s : CompatibleVeroneseSections A π n h (exactVeroneseStep A π hne hgen n h)) :
    exactVeroneseTensorReduction A π n h hne hgen m (1 ⊗ₜ[A] s) =
      boundaryVeroneseEvaluation A π n h (exactVeroneseStep A π hne hgen n h) m s := by
  rw [exactVeroneseTensorReduction, RingEquiv.trans_apply, RingEquiv.trans_apply,
    GradedQuotientTensorComparison.equiv_one_tmul, Ideal.quotEquivOfEq_mk]
  rfl

/-- The tensor reduction preserves and reflects all independently defined stage degrees. -/
theorem exactVeroneseTensorReduction_mem_iff (m d : ℕ) (s) :
    exactVeroneseTensorReduction A π n h hne hgen m s ∈
        boundaryVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h) m d ↔
      s ∈ GradedProjBaseChangeMap.baseGrade
        (B := A ⧸ ideal A π ^ (m + 1))
        (compatibleVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h)) d := by
  constructor
  · intro hs
    obtain ⟨t, ht⟩ := boundaryVeroneseEvaluation_homogeneous_surjective A π n h hne hgen m d
      ⟨exactVeroneseTensorReduction A π n h hne hgen m s, hs⟩
    have he : (1 : A ⧸ ideal A π ^ (m + 1)) ⊗ₜ[A]
        (DirectSum.of _ d t) = s :=
      (exactVeroneseTensorReduction A π n h hne hgen m).injective
        ((exactVeroneseTensorReduction_one_tmul A π n h hne hgen m _).trans ht)
    rw [← he]
    exact Submodule.tmul_mem_baseChange_of_mem 1 ⟨t, rfl⟩
  · intro hs
    obtain ⟨a, ha, he⟩ := (GradedQuotientTensorComparison.equiv_mem_iff
      (compatibleVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h))
      (ideal A π ^ (m + 1)) d s).mpr hs
    have ht : (1 : A ⧸ ideal A π ^ (m + 1)) ⊗ₜ[A] a = s :=
      (GradedQuotientTensorComparison.equiv (ideal A π ^ (m + 1))).injective
        ((GradedQuotientTensorComparison.equiv_one_tmul _ a).trans he)
    rw [← ht, exactVeroneseTensorReduction_one_tmul]
    exact (boundaryVeroneseEvaluation A π n h _ m).map_mem ha

end FLT.Mazur.PolygonArithmeticStages
