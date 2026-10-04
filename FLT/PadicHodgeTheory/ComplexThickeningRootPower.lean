/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexIntegralThickening
public import FLT.PadicHodgeTheory.ComplexRootSequenceShift
public import FLT.GroupScheme.SquareZeroConvolution

/-! # First-order Teichmuller values from any lift of a finite original root -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- At first theta order two, congruent lifts have identical p^s powers. -/
theorem complexThickening_pow_eq_of_theta_eq (s : ℕ)
    (a b : ComplexIntegralThickening p 2 s)
    (h : complexThickeningTheta p 2 s (by decide) a =
      complexThickeningTheta p 2 s (by decide) b) : a ^ (p ^ s) = b ^ (p ^ s) := by
  have hm : a - b ∈ RingHom.ker (complexThickeningTheta p 2 s (by decide)) := by
    change complexThickeningTheta p 2 s (by decide) (a - b) = 0
    rw [map_sub, h, sub_self]
  apply HopfAlgebra.pow_eq_of_sq_zero_sub
  · have hz := Ideal.mul_mem_mul hm hm
    rw [← pow_two, complexThickeningTheta_ker_pow p 2 s (by decide)] at hz
    simpa only [Ideal.mem_bot, pow_two] using hz
  · rw [nsmul_eq_mul, Nat.cast_pow, complexIntegralThickening_prime_pow, zero_mul]

/-- The shifted Teichmuller representative lifts the actual finite root modulo p^s. -/
theorem complexThickening_shift_theta (s : ℕ) (w : Perfection 𝓞_ℂ_[p] p) :
    complexThickeningTheta p 2 s (by decide)
      (Ideal.Quotient.mk (complexThickeningIdeal p 2 s)
        (WittVector.teichmuller p (complexRootSequenceShift p w s))) =
      Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ s}) (w.val s) := by
  change Ideal.Quotient.mk _ (complexTheta p
    (WittVector.teichmuller p (complexRootSequenceShift p w s))) = _
  rw [complexTheta_teichmuller, complexRootSequenceShift_sharp]

/-- Raising that lift to p^s gives the original unshifted Teichmuller value. -/
theorem complexThickening_shift_pow (s : ℕ) (w : Perfection 𝓞_ℂ_[p] p) :
    Ideal.Quotient.mk (complexThickeningIdeal p 2 s)
        (WittVector.teichmuller p (complexRootSequenceShift p w s)) ^ (p ^ s) =
      Ideal.Quotient.mk (complexThickeningIdeal p 2 s)
        (WittVector.teichmuller p (complexRootSequenceShift p w 0)) := by
  rw [← map_pow, ← map_pow, complexRootSequenceShift_pow_prime_pow]

/-- Any lift of the actual finite root computes the same first-order Teichmuller value. -/
theorem complexThickening_root_lift_pow (s : ℕ) (w : Perfection 𝓞_ℂ_[p] p)
    (a : ComplexIntegralThickening p 2 s)
    (ha : complexThickeningTheta p 2 s (by decide) a =
      Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ s}) (w.val s)) :
    a ^ (p ^ s) = Ideal.Quotient.mk (complexThickeningIdeal p 2 s)
      (WittVector.teichmuller p (complexRootSequenceShift p w 0)) :=
  (complexThickening_pow_eq_of_theta_eq p s a _
    (ha.trans (complexThickening_shift_theta p s w).symm)).trans
      (complexThickening_shift_pow p s w)

end PadicHodgeTheory
