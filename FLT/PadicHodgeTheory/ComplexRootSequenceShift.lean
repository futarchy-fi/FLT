/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexCyclotomicTilt

/-! # Shifted actual integral root sequences and their sharp values -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Discard the first n entries of the actual compatible root sequence. -/
def complexRootSequenceTail (s : Perfection 𝓞_ℂ_[p] p) (n : ℕ) : Perfection 𝓞_ℂ_[p] p :=
  ⟨fun k ↦ s.val (k + n), fun k ↦ by
    simpa only [Nat.add_right_comm] using s.property (k + n)⟩

/-- Shift any actual compatible integral root sequence before reducing to the tilt. -/
def complexRootSequenceShift (s : Perfection 𝓞_ℂ_[p] p) (n : ℕ) : IntegralTilt p :=
  Perfection.quotientMulEquiv p (Ideal.span {(p : 𝓞_ℂ_[p])}) (complexRootSequenceTail p s n)

/-- The sharp of the shifted sequence is precisely its original nth root. -/
theorem complexRootSequenceShift_sharp (s : Perfection 𝓞_ℂ_[p] p) (n : ℕ) :
    complexSharp p (complexRootSequenceShift p s n) = s.val n := by
  have h := Perfection.coeff_zero_symm_quotientMulEquiv (complexRootSequenceShift p s n)
  rw [complexRootSequenceShift, MulEquiv.symm_apply_apply] at h
  change s.val (0 + n) = complexSharp p (complexRootSequenceShift p s n) at h
  simpa only [Nat.zero_add] using h.symm

/-- One pth power removes one shift in the original roots. -/
theorem complexRootSequenceShift_pow (s : Perfection 𝓞_ℂ_[p] p) (n : ℕ) :
    complexRootSequenceShift p s (n + 1) ^ p = complexRootSequenceShift p s n := by
  change (Perfection.quotientMulEquiv p (Ideal.span {(p : 𝓞_ℂ_[p])}))
    (complexRootSequenceTail p s (n + 1)) ^ p =
      (Perfection.quotientMulEquiv p (Ideal.span {(p : 𝓞_ℂ_[p])}))
        (complexRootSequenceTail p s n)
  rw [← map_pow]
  congr 1
  apply Perfection.extMonoid
  intro k
  exact s.property (k + n)

/-- Taking p^n powers removes all n shifts before any coefficient inversion. -/
theorem complexRootSequenceShift_pow_prime_pow (s : Perfection 𝓞_ℂ_[p] p) (n : ℕ) :
    complexRootSequenceShift p s n ^ (p ^ n) = complexRootSequenceShift p s 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, complexRootSequenceShift_pow, ih]

end PadicHodgeTheory
