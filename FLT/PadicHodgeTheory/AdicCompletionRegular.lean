/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Regularity of the parameter in a principal-ideal completion -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable {R : Type*} [CommRing R] [IsDomain R]

/-- Cancellation one level higher makes the completed parameter a non-zero-divisor. -/
theorem adicCompletion_parameter_mul_eq_zero (t : R) (ht : t ≠ 0)
    (x : AdicCompletion (Ideal.span {t}) R)
    (hx : algebraMap R (AdicCompletion (Ideal.span {t}) R) t * x = 0) : x = 0 := by
  let I : Ideal R := Ideal.span {t}
  induction x using AdicCompletion.induction_on I R with
  | h f =>
    apply AdicCompletion.ext_evalₐ
    intro n
    have he := congrArg (AdicCompletion.evalₐ I (n + 1)) hx
    change AdicCompletion.evalₐ I (n + 1)
      (AdicCompletion.of I R t * AdicCompletion.mk I R f) =
        AdicCompletion.evalₐ I (n + 1) 0 at he
    have ha : t * f.val (n + 1) ∈ I ^ (n + 1) := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [map_mul, map_zero, AdicCompletion.evalₐ_mk,
        AdicCompletion.evalₐ_of] using he
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
    obtain ⟨b, hb⟩ := ha
    have hb' : f.val (n + 1) = t ^ n * b := by
      apply mul_left_cancel₀ ht
      calc t * f.val (n + 1) = t ^ (n + 1) * b := hb
           _ = t * (t ^ n * b) := by rw [pow_succ]; ring
    rw [map_zero, AdicCompletion.evalₐ_mk,
      ← AdicCompletion.Ideal.mk_eq_mk I (Nat.le_succ n) f]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, hb']
    exact dvd_mul_right _ _

/-- The regularity result with an explicitly identified principal completion ideal. -/
theorem adicCompletion_parameter_mul_eq_zero_of_span (I : Ideal R) (t : R)
    (hI : I = Ideal.span {t}) (ht : t ≠ 0) (x : AdicCompletion I R)
    (hx : algebraMap R (AdicCompletion I R) t * x = 0) : x = 0 := by
  subst I
  exact adicCompletion_parameter_mul_eq_zero t ht x hx

end PadicHodgeTheory
