/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.AdicSeries
public import FLT.PadicHodgeTheory.ComplexCyclotomicTilt
public import FLT.PadicHodgeTheory.ComplexDeRhamEquivariance

/-! # The cyclotomic logarithmic sum in the actual B_dR^+

This constructs the sum and its finite congruences. Nonvanishing, order one
and the p-adic cyclotomic scalar formula require separate proofs.
-/

@[expose] public noncomputable section
namespace PadicHodgeTheory
open Finset
variable (p : ℕ) [Fact p.Prime]

/-- Every positive integer is a unit in the actual de Rham local ring. -/
theorem complexDeRhamNat_isUnit (n : ℕ) (hn : n ≠ 0) :
    IsUnit (n : ComplexBDeRhamPlus p) := by
  by_contra h
  have hm : (n : ComplexBDeRhamPlus p) ∈ IsLocalRing.maximalIdeal (ComplexBDeRhamPlus p) := h
  rw [complexDeRham_maximalIdeal, ← complexDeRhamTheta_ker] at hm
  have he : complexDeRhamTheta p (n : ComplexBDeRhamPlus p) = 0 := hm
  rw [map_natCast] at he
  exact (Nat.cast_ne_zero.mpr hn) he

/-- The actual completed cyclotomic difference [epsilon] - 1. -/
def complexCyclotomicArgument : ComplexBDeRhamPlus p :=
  algebraMap (ComplexAinfInvertP p) (ComplexBDeRhamPlus p)
    (algebraMap (Ainf p) (ComplexAinfInvertP p) (complexCyclotomicDifference p))

/-- Its theta image vanishes, so it is an admissible adic logarithm argument. -/
theorem complexCyclotomicArgument_mem :
    complexCyclotomicArgument p ∈ Ideal.span {complexDeRhamParameter p} := by
  rw [← complexDeRhamTheta_ker]
  change complexDeRhamTheta p (complexCyclotomicArgument p) = 0
  rw [complexCyclotomicArgument, complexDeRhamTheta_algebraMap,
    show complexTheta p (complexCyclotomicDifference p) = 0 from
      complexCyclotomicDifference_mem_ker p]
  rfl

/-- Rational logarithm coefficients, using actual inverses of the unit denominators. -/
def complexLogCoefficient : ℕ → ComplexBDeRhamPlus p
  | 0 => 0
  | n + 1 => (-1) ^ n * Ring.inverse (n + 1 : ComplexBDeRhamPlus p)

/-- The denominator inverse used in each coefficient is a genuine inverse. -/
theorem complexLogCoefficient_denominator (n : ℕ) :
    (n + 1 : ComplexBDeRhamPlus p) * Ring.inverse (n + 1 : ComplexBDeRhamPlus p) = 1 :=
  Ring.mul_inverse_cancel _ (by
    simpa only [Nat.cast_add, Nat.cast_one] using
      complexDeRhamNat_isUnit p (n + 1) (Nat.succ_ne_zero n))

/-- Every term of the logarithm lies in the corresponding filtration level. -/
theorem complexCyclotomicLog_term_mem (n : ℕ) :
    complexLogCoefficient p n * complexCyclotomicArgument p ^ n ∈
      Ideal.span {complexDeRhamParameter p} ^ n :=
  Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (complexCyclotomicArgument_mem p) n)

/-- The actual logarithmic sum t = log([epsilon]) in B_dR^+. -/
def complexCyclotomicLog : ComplexBDeRhamPlus p :=
  adicSeries (Ideal.span {complexDeRhamParameter p})
    (fun n ↦ complexLogCoefficient p n * complexCyclotomicArgument p ^ n)
    (complexCyclotomicLog_term_mem p)

/-- Every finite truncation agrees with t to its specified adic order. -/
theorem complexCyclotomicLog_truncation (n : ℕ) :
    complexCyclotomicLog p ≡
      (∑ k ∈ range n, complexLogCoefficient p k * complexCyclotomicArgument p ^ k)
        [SMOD ((Ideal.span {complexDeRhamParameter p}) ^ n • ⊤ : Ideal (ComplexBDeRhamPlus p))] :=
  (adicSeries_spec _ _ _ n).symm

/-- The logarithm belongs to the first filtration step. -/
theorem complexCyclotomicLog_mem :
    complexCyclotomicLog p ∈ Ideal.span {complexDeRhamParameter p} := by
  have h := complexCyclotomicLog_truncation p 1
  rw [SModEq.sub_mem] at h
  simpa [complexLogCoefficient] using h

/-- Modulo the square of the parameter ideal, the logarithm is its linear term. -/
theorem complexCyclotomicLog_sub_argument_mem :
    complexCyclotomicLog p - complexCyclotomicArgument p ∈
      Ideal.span {complexDeRhamParameter p} ^ 2 := by
  have h := complexCyclotomicLog_truncation p 2
  rw [SModEq.sub_mem] at h
  simpa [sum_range_succ, complexLogCoefficient, Ring.inverse_one] using h

end PadicHodgeTheory
