/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexSharpSurjective
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Compatible primitive p-power roots in the actual integer ring -/

@[expose] public noncomputable section
open scoped NNReal
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- A primitive p-th root in C_p is integral. -/
theorem complexInteger_exists_primitiveRoot : ∃ x : 𝓞_ℂ_[p], IsPrimitiveRoot x p := by
  obtain ⟨x, hx⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[p] p
  have hint : x ∈ PadicComplexInt p := by
    change Valued.v x ≤ 1
    apply (pow_le_one_iff_of_nonneg (zero_le : (0 : ℝ≥0) ≤ Valued.v x)
      (Fact.out : p.Prime).ne_zero).mp
    rw [← map_pow, hx.pow_eq_one, map_one]
  refine ⟨⟨x, hint⟩, ?_⟩
  exact (IsPrimitiveRoot.map_iff_of_injective (f := (PadicComplexInt p).subtype)
    Subtype.val_injective).mp hx

/-- Fix a primitive root at the first nontrivial cyclotomic level. -/
def complexCyclotomicRoot : 𝓞_ℂ_[p] := (complexInteger_exists_primitiveRoot p).choose

/-- The chosen root is primitive. -/
theorem complexCyclotomicRoot_primitive : IsPrimitiveRoot (complexCyclotomicRoot p) p :=
  (complexInteger_exists_primitiveRoot p).choose_spec

/-- A compatible root system, starting at one and then the chosen primitive root. -/
def complexCyclotomicSequence : Perfection 𝓞_ℂ_[p] p :=
  ⟨fun n ↦ match n with
    | 0 => 1
    | n + 1 => (complexIntegerRoot p)^[n] (complexCyclotomicRoot p), fun n ↦ by
    cases n with
    | zero => exact (complexCyclotomicRoot_primitive p).pow_eq_one
    | succ n =>
      change ((complexIntegerRoot p)^[n + 1] (complexCyclotomicRoot p)) ^ p = _
      rw [Function.iterate_succ_apply', complexIntegerRoot_pow]⟩

/-- Every higher root has the prescribed first-level ancestor. -/
theorem complexCyclotomicSequence_pow (n : ℕ) :
    (complexCyclotomicSequence p).val (n + 1) ^ (p ^ n) = complexCyclotomicRoot p := by
  induction n with
  | zero => simp [complexCyclotomicSequence]
  | succ n ih =>
    rw [pow_succ', pow_mul, (complexCyclotomicSequence p).property (n + 1), ih]

/-- Every coordinate has exactly the required p-power order. -/
theorem complexCyclotomicSequence_primitive (n : ℕ) :
    IsPrimitiveRoot ((complexCyclotomicSequence p).val n) (p ^ n) := by
  cases n with
  | zero => simp [complexCyclotomicSequence]
  | succ n =>
    have hnot : (complexCyclotomicSequence p).val (n + 1) ^ (p ^ n) ≠ 1 := by
      rw [complexCyclotomicSequence_pow]
      exact (complexCyclotomicRoot_primitive p).ne_one (Fact.out : p.Prime).one_lt
    have hfin : (complexCyclotomicSequence p).val (n + 1) ^ (p ^ (n + 1)) = 1 := by
      rw [pow_succ, pow_mul, complexCyclotomicSequence_pow]
      exact (complexCyclotomicRoot_primitive p).pow_eq_one
    rw [← orderOf_eq_prime_pow hnot hfin]
    exact IsPrimitiveRoot.orderOf _

end PadicHodgeTheory
