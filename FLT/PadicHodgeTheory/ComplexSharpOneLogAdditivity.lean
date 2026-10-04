/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexSharpOneLog
public import FLT.PadicHodgeTheory.ComplexFiniteLogEvaluation
public import FLT.PadicHodgeTheory.NilpotentLogProduct

/-! # Multiplicativity becomes additivity for the actual sharp-one logarithm -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The actual sharp-one logarithm evaluates to the finite logarithm at each theta quotient. -/
theorem complexTiltLog_eval (z : IntegralTilt p) (hz : complexSharp p z = 1) (r : ℕ) :
    complexDeRhamFiniteEval p r (complexTiltLog p z hz) =
      finiteNilpotentLog r (complexDeRhamFiniteEval p r (complexTiltLogArgument p z)) := by
  have h := complexTiltLog_truncation p z hz r
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

/-- The actual Teichmuller differences obey the original multiplication law. -/
theorem complexTiltLogArgument_mul (z w : IntegralTilt p) :
    complexTiltLogArgument p (z * w) =
      (1 + complexTiltLogArgument p z) * (1 + complexTiltLogArgument p w) - 1 := by
  simp only [complexTiltLogArgument, map_mul, map_sub, map_one]
  ring

/-- The convergent sharp-one logarithm sends products to sums in the existing de Rham ring. -/
theorem complexTiltLog_mul (z w : IntegralTilt p)
    (hz : complexSharp p z = 1) (hw : complexSharp p w = 1) :
    complexTiltLog p (z * w) (by rw [map_mul, hz, hw, one_mul]) =
      complexTiltLog p z hz + complexTiltLog p w hw := by
  apply AdicCompletion.ext_evalₐ
  intro r
  change complexDeRhamFiniteEval p r (complexTiltLog p (z * w) _) =
    complexDeRhamFiniteEval p r (complexTiltLog p z hz + complexTiltLog p w hw)
  rw [map_add, complexTiltLog_eval, complexTiltLog_eval, complexTiltLog_eval,
    complexTiltLogArgument_mul, map_sub, map_mul, map_add, map_add, map_one]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp (complexTiltLogArgument_mem p z hz)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (complexTiltLogArgument_mem p w hw)
  rw [ha, hb, map_mul, map_mul]
  apply finiteNilpotentLog_mul
  rw [← map_pow]
  apply complexDeRhamFiniteEval_eq_zero
  exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) r

/-- The trivial compatible root sequence has zero actual logarithm. -/
@[simp] theorem complexTiltLog_one : complexTiltLog p 1 (map_one _) = 0 := by
  have h := complexTiltLog_mul p 1 1 (map_one _) (map_one _)
  simp only [one_mul] at h
  exact (add_eq_left.mp h.symm)

end PadicHodgeTheory
