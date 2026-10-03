/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexFiniteLogAlgebra
public import FLT.PadicHodgeTheory.ComplexCyclotomicLogTransport
public import FLT.PadicHodgeTheory.NilpotentLogPower

/-! # The original cyclotomic logarithm at each finite theta level -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- A concise name for the existing finite-level evaluation. -/
def complexDeRhamFiniteEval (r : ℕ) : ComplexBDeRhamPlus p →+* ComplexFiniteThetaQuotient p r :=
  (AdicCompletion.evalₐ (ComplexDeRhamIdeal p) r).toRingHom

/-- The evaluation kills the corresponding completed parameter power. -/
theorem complexDeRhamFiniteEval_eq_zero (r : ℕ) {x : ComplexBDeRhamPlus p}
    (hx : x ∈ Ideal.span {complexDeRhamParameter p} ^ r) :
    complexDeRhamFiniteEval p r x = 0 := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨a, rfl⟩ := hx
  rw [map_mul, map_pow]
  have hz : complexDeRhamFiniteEval p r (complexDeRhamParameter p) ^ r = 0 := by
    change (Ideal.Quotient.mk (ComplexDeRhamIdeal p ^ r)
      (algebraMap (Ainf p) (ComplexAinfInvertP p) (complexThetaGenerator p))) ^ r = 0
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    apply Ideal.pow_mem_pow
    rw [ComplexDeRhamIdeal, complexThetaInvertP_ker_eq_span]
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [hz, zero_mul]

/-- The completed cyclotomic argument becomes nilpotent at every finite level. -/
theorem complexCyclotomicArgument_eval_nilpotent (r : ℕ) :
    complexDeRhamFiniteEval p r (complexCyclotomicArgument p) ^ r = 0 := by
  rw [← map_pow]
  exact complexDeRhamFiniteEval_eq_zero p r
    (Ideal.pow_mem_pow (complexCyclotomicArgument_mem p) r)

/-- Evaluating the actual t gives precisely the finite logarithm polynomial. -/
theorem complexCyclotomicLog_eval (r : ℕ) :
    complexDeRhamFiniteEval p r (complexCyclotomicLog p) =
      finiteNilpotentLog r (complexDeRhamFiniteEval p r (complexCyclotomicArgument p)) := by
  have h := complexCyclotomicLog_truncation p r
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
  have he := complexDeRhamFiniteEval_eq_zero p r h
  rw [map_sub, sub_eq_zero] at he
  rw [he, map_sum]
  unfold finiteNilpotentLog
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul, map_pow]
  congr 1
  exact complexLogCoefficient_eval p r k

/-- Evaluating sigma(t) gives the finite logarithm at the actual transformed argument. -/
theorem complexCyclotomicLog_galois_eval (σ : PadicGalois p) (r : ℕ) :
    complexDeRhamFiniteEval p r (complexDeRhamGalois p σ (complexCyclotomicLog p)) =
      finiteNilpotentLog r
        (complexDeRhamFiniteEval p r (complexDeRhamGalois p σ (complexCyclotomicArgument p))) := by
  have h := complexCyclotomicLog_truncation p r
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
  have he := complexDeRhamFiniteEval_eq_zero p r
    ((complexDeRhamGalois_mem_filtration_iff p σ _ r).mpr h)
  rw [map_sub, map_sub, sub_eq_zero] at he
  rw [he, map_sum, map_sum]
  unfold finiteNilpotentLog
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul, map_mul, map_pow, map_pow, complexLogCoefficient_galois]
  congr 1
  exact complexLogCoefficient_eval p r k

/-- Finite evaluation of the original argument uses the canonical localized quotient. -/
theorem complexCyclotomicArgument_eval (r : ℕ) :
    complexDeRhamFiniteEval p r (complexCyclotomicArgument p) =
      Ideal.Quotient.mk (ComplexDeRhamIdeal p ^ r)
        (algebraMap (Ainf p) (ComplexAinfInvertP p)
          (WittVector.teichmuller p (complexCyclotomicTilt p))) - 1 := by
  change Ideal.Quotient.mk (ComplexDeRhamIdeal p ^ r)
    (algebraMap (Ainf p) (ComplexAinfInvertP p) (complexCyclotomicDifference p)) = _
  simp only [complexCyclotomicDifference, map_sub, map_one]

/-- Finite evaluation of the transformed argument uses the actual transformed epsilon. -/
theorem complexCyclotomicArgument_galois_eval (σ : PadicGalois p) (r : ℕ) :
    complexDeRhamFiniteEval p r (complexDeRhamGalois p σ (complexCyclotomicArgument p)) =
      Ideal.Quotient.mk (ComplexDeRhamIdeal p ^ r)
        (algebraMap (Ainf p) (ComplexAinfInvertP p)
          (WittVector.teichmuller p (complexTiltGalois p σ (complexCyclotomicTilt p)))) - 1 := by
  rw [complexCyclotomicArgument_galois]
  change Ideal.Quotient.mk (ComplexDeRhamIdeal p ^ r)
    (algebraMap (Ainf p) (ComplexAinfInvertP p) _) = _
  simp only [map_sub, map_one]

end PadicHodgeTheory
