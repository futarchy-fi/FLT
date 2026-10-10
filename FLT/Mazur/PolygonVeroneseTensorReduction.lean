/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonStageVeroneseGrading
public import FLT.Mazur.GradedQuotientTensorComparison

/-!
# Original stage reduction as graded coefficient base change

The actual parameter-power quotient is the tensor product with the truncated
coefficient ring. Its existing evaluation equivalence preserves and reflects
the independently constructed original stage degrees.
-/

@[expose] public noncomputable section

open scoped TensorProduct DirectSum

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval boundaryLine family

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original coefficient ideal power maps to the actual compatible parameter ideal power. -/
theorem exactVeroneseParameter_map (m : ℕ) :
    (parameterIdeal K ^ (m + 1)).map
        (algebraMap (PowerSeries K)
          (CompatibleVeroneseSections K n h (exactVeroneseStep K n h))) =
      compatibleVeroneseParameterIdeal K n h (exactVeroneseStep K n h) ^ (m + 1) := by
  rw [Ideal.map_pow, parameterIdeal, compatibleVeroneseParameterIdeal,
    Ideal.map_span, Set.image_singleton]

/-- The actual stage evaluation is an equivalence from coefficient scalar extension. -/
def exactVeroneseTensorReduction (m : ℕ) :
    (PowerSeries K ⧸ parameterIdeal K ^ (m + 1)) ⊗[PowerSeries K]
        CompatibleVeroneseSections K n h (exactVeroneseStep K n h) ≃+*
      boundaryVeroneseRing K n h (exactVeroneseStep K n h) m :=
  ((GradedQuotientTensorComparison.equiv (parameterIdeal K ^ (m + 1))).trans
    (Ideal.quotEquivOfEq (exactVeroneseParameter_map K n h m))).trans
      (exactVeroneseAdicReduction K n h m)

/-- Scalar extension retains every original compatible evaluation. -/
theorem exactVeroneseTensorReduction_one_tmul (m : ℕ)
    (s : CompatibleVeroneseSections K n h (exactVeroneseStep K n h)) :
    exactVeroneseTensorReduction K n h m (1 ⊗ₜ[PowerSeries K] s) =
      boundaryVeroneseEvaluation K n h (exactVeroneseStep K n h) m s := by
  rw [exactVeroneseTensorReduction, RingEquiv.trans_apply, RingEquiv.trans_apply,
    GradedQuotientTensorComparison.equiv_one_tmul, Ideal.quotEquivOfEq_mk]
  rfl

/-- The tensor reduction preserves and reflects all independently defined stage degrees. -/
theorem exactVeroneseTensorReduction_mem_iff (m d : ℕ) (s) :
    exactVeroneseTensorReduction K n h m s ∈
        boundaryVeroneseGrade K n h (exactVeroneseStep K n h) m d ↔
      s ∈ GradedProjBaseChangeMap.baseGrade
        (B := PowerSeries K ⧸ parameterIdeal K ^ (m + 1))
        (compatibleVeroneseGrade K n h (exactVeroneseStep K n h)) d := by
  constructor
  · intro hs
    obtain ⟨t, ht⟩ := boundaryVeroneseEvaluation_homogeneous_surjective K n h m d
      ⟨exactVeroneseTensorReduction K n h m s, hs⟩
    have he : (1 : PowerSeries K ⧸ parameterIdeal K ^ (m + 1)) ⊗ₜ[PowerSeries K]
        (DirectSum.of _ d t) = s :=
      (exactVeroneseTensorReduction K n h m).injective
        ((exactVeroneseTensorReduction_one_tmul K n h m _).trans ht)
    rw [← he]
    exact Submodule.tmul_mem_baseChange_of_mem 1 ⟨t, rfl⟩
  · intro hs
    obtain ⟨a, ha, he⟩ := (GradedQuotientTensorComparison.equiv_mem_iff
      (compatibleVeroneseGrade K n h (exactVeroneseStep K n h))
      (parameterIdeal K ^ (m + 1)) d s).mpr hs
    have ht : (1 : PowerSeries K ⧸ parameterIdeal K ^ (m + 1)) ⊗ₜ[PowerSeries K] a = s :=
      (GradedQuotientTensorComparison.equiv (parameterIdeal K ^ (m + 1))).injective
        ((GradedQuotientTensorComparison.equiv_one_tmul _ a).trans he)
    rw [← ht, exactVeroneseTensorReduction_one_tmul]
    exact (boundaryVeroneseEvaluation K n h _ m).map_mem ha

end FLT.Mazur.PolygonInfinitesimalStages
