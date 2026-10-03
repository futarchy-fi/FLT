/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexCyclotomicRoots

/-! # The cyclotomic element in the actual integral tilt -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Epsilon is the reduction of the constructed primitive-root sequence. -/
def complexCyclotomicTilt : IntegralTilt p :=
  Perfection.quotientMulEquiv p (Ideal.span {(p : 𝓞_ℂ_[p])}) (complexCyclotomicSequence p)

/-- The multiplicative lift of epsilon is the actual primitive-root sequence. -/
theorem complexCyclotomicTilt_lift :
    (Perfection.quotientMulEquiv p (Ideal.span {(p : 𝓞_ℂ_[p])})).symm
      (complexCyclotomicTilt p) = complexCyclotomicSequence p :=
  (Perfection.quotientMulEquiv p (Ideal.span {(p : 𝓞_ℂ_[p])})).symm_apply_apply _

/-- Sharp of epsilon is one. -/
@[simp] theorem complexCyclotomicTilt_sharp : complexSharp p (complexCyclotomicTilt p) = 1 := by
  have h := Perfection.coeff_zero_symm_quotientMulEquiv (complexCyclotomicTilt p)
  rw [complexCyclotomicTilt_lift] at h
  exact h.symm

/-- Epsilon is not the constant one element of the tilt. -/
theorem complexCyclotomicTilt_ne_one : complexCyclotomicTilt p ≠ 1 := by
  intro h
  have he : complexCyclotomicSequence p = 1 := by
    apply (Perfection.quotientMulEquiv p (Ideal.span {(p : 𝓞_ℂ_[p])})).injective
    exact h.trans (map_one _).symm
  have hc := congrArg (Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 1) he
  exact (complexCyclotomicRoot_primitive p).ne_one (Fact.out : p.Prime).one_lt hc

/-- The cyclotomic logarithm's argument minus one, in the actual Witt ring. -/
def complexCyclotomicDifference : Ainf p := WittVector.teichmuller p (complexCyclotomicTilt p) - 1

/-- The cyclotomic difference belongs to the actual theta kernel. -/
theorem complexCyclotomicDifference_mem_ker :
    complexCyclotomicDifference p ∈ RingHom.ker (complexTheta p) := by
  change complexTheta p (WittVector.teichmuller p (complexCyclotomicTilt p) - 1) = 0
  rw [map_sub, complexTheta_teichmuller, complexCyclotomicTilt_sharp, map_one, sub_self]

/-- The argument minus one is nonzero before localization and completion. -/
theorem complexCyclotomicDifference_ne_zero : complexCyclotomicDifference p ≠ 0 := by
  intro h
  have hc := congrArg (fun x : Ainf p ↦ x.coeff 0) (sub_eq_zero.mp h)
  exact complexCyclotomicTilt_ne_one p (by simpa using hc)

end PadicHodgeTheory
