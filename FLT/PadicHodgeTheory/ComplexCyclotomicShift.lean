/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexCyclotomicTilt

/-! # Shifted cyclotomic elements and their actual sharp values -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The compatible root sequence with its first n entries removed. -/
def complexCyclotomicShiftSequence (n : ℕ) : Perfection 𝓞_ℂ_[p] p :=
  ⟨fun k ↦ (complexCyclotomicSequence p).val (k + n), fun k ↦ by
    simpa only [Nat.add_right_comm] using (complexCyclotomicSequence p).property (k + n)⟩

/-- Shift the compatible cyclotomic roots by n places before reduction. -/
def complexCyclotomicShift (n : ℕ) : IntegralTilt p :=
  Perfection.quotientMulEquiv p (Ideal.span {(p : 𝓞_ℂ_[p])})
    (complexCyclotomicShiftSequence p n)

/-- With no shift this is epsilon itself. -/
@[simp] theorem complexCyclotomicShift_zero :
    complexCyclotomicShift p 0 = complexCyclotomicTilt p := rfl

/-- The multiplicative sharp value is the actual nth root in the chosen sequence. -/
@[simp] theorem complexCyclotomicShift_sharp (n : ℕ) :
    complexSharp p (complexCyclotomicShift p n) = (complexCyclotomicSequence p).val n := by
  have h := Perfection.coeff_zero_symm_quotientMulEquiv (complexCyclotomicShift p n)
  rw [complexCyclotomicShift, MulEquiv.symm_apply_apply] at h
  change (complexCyclotomicSequence p).val (0 + n) =
    complexSharp p (complexCyclotomicShift p n) at h
  simpa only [Nat.zero_add] using h.symm

/-- Taking the pth power removes one shift. -/
theorem complexCyclotomicShift_pow (n : ℕ) :
    complexCyclotomicShift p (n + 1) ^ p = complexCyclotomicShift p n := by
  change (Perfection.quotientMulEquiv p (Ideal.span {(p : 𝓞_ℂ_[p])}))
    (complexCyclotomicShiftSequence p (n + 1)) ^ p =
    (Perfection.quotientMulEquiv p (Ideal.span {(p : 𝓞_ℂ_[p])}))
      (complexCyclotomicShiftSequence p n)
  rw [← map_pow]
  congr 1
  apply Perfection.extMonoid
  intro k
  exact (complexCyclotomicSequence p).property (k + n)

/-- One inverse Frobenius step is the first shifted element. -/
theorem complexCyclotomicShift_frobenius (n : ℕ) :
    (frobeniusEquiv (IntegralTilt p) p).symm (complexCyclotomicShift p n) =
      complexCyclotomicShift p (n + 1) := by
  apply (frobeniusEquiv (IntegralTilt p) p).injective
  simpa only [RingEquiv.apply_symm_apply, frobeniusEquiv_apply, frobenius_def] using
    (complexCyclotomicShift_pow p n).symm

/-- The first shift has sharp the primitive pth root, rather than one. -/
theorem complexCyclotomicShift_one_sharp :
    complexSharp p (complexCyclotomicShift p 1) = complexCyclotomicRoot p :=
  complexCyclotomicShift_sharp p 1

/-- Each positive shift has nontrivial sharp value. -/
theorem complexCyclotomicShift_sharp_ne_one (n : ℕ) :
    complexSharp p (complexCyclotomicShift p (n + 1)) ≠ 1 := by
  rw [complexCyclotomicShift_sharp]
  exact (complexCyclotomicSequence_primitive p (n + 1)).ne_one
    (one_lt_pow₀ (Fact.out : p.Prime).one_lt (Nat.succ_ne_zero n))

end PadicHodgeTheory
