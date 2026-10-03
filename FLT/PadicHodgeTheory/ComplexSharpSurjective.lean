/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexFontaineTheta

/-! # Surjectivity of sharp from compatible integral p-power roots -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- A chosen p-th root in the actual integer ring. -/
def complexIntegerRoot (x : 𝓞_ℂ_[p]) : 𝓞_ℂ_[p] :=
  (complexInteger_pow_surjective p x).choose

/-- The chosen root has the required power. -/
@[simp] theorem complexIntegerRoot_pow (x : 𝓞_ℂ_[p]) :
    complexIntegerRoot p x ^ p = x :=
  (complexInteger_pow_surjective p x).choose_spec

/-- Iterated roots form a compatible multiplicative sequence starting at x. -/
def complexIntegerRootSequence (x : 𝓞_ℂ_[p]) : Perfection 𝓞_ℂ_[p] p :=
  ⟨fun n ↦ (complexIntegerRoot p)^[n] x, fun n ↦ by
    change ((complexIntegerRoot p)^[n + 1] x) ^ p = (complexIntegerRoot p)^[n] x
    rw [Function.iterate_succ_apply', complexIntegerRoot_pow]⟩

/-- Its zeroth coordinate is the prescribed integer. -/
@[simp] theorem complexIntegerRootSequence_zero (x : 𝓞_ℂ_[p]) :
    Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 (complexIntegerRootSequence p x) = x := rfl

/-- Reduction of the compatible sequence produces a sharp lift of every integer. -/
theorem complexSharp_surjective : Function.Surjective (complexSharp p) := by
  intro x
  let e := Perfection.quotientMulEquiv p (Ideal.span {(p : 𝓞_ℂ_[p])})
  refine ⟨e (complexIntegerRootSequence p x), ?_⟩
  have h : Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0
      (e.symm (e (complexIntegerRootSequence p x))) =
      complexSharp p (e (complexIntegerRootSequence p x)) :=
    Perfection.coeff_zero_symm_quotientMulEquiv _
  rw [e.symm_apply_apply, complexIntegerRootSequence_zero] at h
  exact h.symm

end PadicHodgeTheory
