/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.AdicLinearTerm
public import FLT.PadicHodgeTheory.ComplexCyclotomicCompleted

/-! # The actual cyclotomic logarithm has order one -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The logarithm and its linear term differ by a unit factor. -/
theorem complexCyclotomicLog_associated_argument :
    Associated (complexCyclotomicArgument p) (complexCyclotomicLog p) := by
  have he : Ideal.span {complexCyclotomicArgument p} =
      Ideal.span {complexDeRhamParameter p} := by
    rw [complexCyclotomicArgument_span, complexDeRham_maximalIdeal]
  let : IsAdicComplete (Ideal.span {complexCyclotomicArgument p}) (ComplexBDeRhamPlus p) := by
    rw [he]
    infer_instance
  apply associated_of_adic_linear_term
  rw [he]
  exact complexCyclotomicLog_sub_argument_mem p

/-- The logarithm is associated to the original completed theta parameter. -/
theorem complexCyclotomicLog_associated :
    Associated (complexDeRhamParameter p) (complexCyclotomicLog p) :=
  (complexCyclotomicArgument_associated p).trans (complexCyclotomicLog_associated_argument p)

/-- The actual logarithmic period is a uniformizer. -/
theorem complexCyclotomicLog_irreducible : Irreducible (complexCyclotomicLog p) :=
  (complexCyclotomicLog_associated p).irreducible (complexDeRhamParameter_irreducible p)

/-- In particular the actual logarithmic sum is nonzero. -/
theorem complexCyclotomicLog_ne_zero : complexCyclotomicLog p ≠ 0 :=
  (complexCyclotomicLog_irreducible p).ne_zero

/-- The period generates the maximal ideal of the actual de Rham ring. -/
theorem complexCyclotomicLog_span :
    Ideal.span {complexCyclotomicLog p} =
      IsLocalRing.maximalIdeal (ComplexBDeRhamPlus p) := by
  rw [complexDeRham_maximalIdeal]
  exact Ideal.span_singleton_eq_span_singleton.mpr (complexCyclotomicLog_associated p).symm

/-- The completed cyclotomic difference has exactly order one. -/
theorem complexCyclotomicArgument_notMem_square :
    complexCyclotomicArgument p ∉ Ideal.span {complexDeRhamParameter p} ^ 2 := by
  rw [← complexDeRham_maximalIdeal, ← complexCyclotomicArgument_span]
  exact notMem_square_span_self _ (complexCyclotomicArgument_ne_zero p)
    (complexCyclotomicArgument_irreducible p).not_isUnit

/-- The logarithmic period also has exactly order one. -/
theorem complexCyclotomicLog_notMem_square :
    complexCyclotomicLog p ∉ Ideal.span {complexDeRhamParameter p} ^ 2 := by
  rw [← complexDeRham_maximalIdeal, ← complexCyclotomicLog_span]
  exact notMem_square_span_self _ (complexCyclotomicLog_ne_zero p)
    (complexCyclotomicLog_irreducible p).not_isUnit

/-- Powers of t give the original nonnegative filtration. -/
theorem complexCyclotomicLog_filtration (n : ℕ) :
    Ideal.span {complexCyclotomicLog p ^ n} = Ideal.span {complexDeRhamParameter p} ^ n := by
  rw [← Ideal.span_singleton_pow, complexCyclotomicLog_span, complexDeRham_maximalIdeal]

end PadicHodgeTheory
