/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicFilteredAlgebraHom

/-!
# Ideal containment constructs continuous extensions

Sending the source ideal into the extended target ideal suffices for every
power-filtration compatibility, and therefore constructs an algebra map on
completions without assuming any extension as input.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicIdealFilteredMap

open AdicCompletion

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (I : Ideal A) (J : Ideal B) (f : A →ₐ[R] AdicCompletion J B)
  (hf : I.map f.toRingHom ≤ J.map (algebraMap B (AdicCompletion J B)))

/-- The extended target ideal to the nth power dies under nth-order evaluation. -/
theorem pow_le_ker_eval (n : ℕ) :
    (J.map (algebraMap B (AdicCompletion J B))) ^ n ≤ RingHom.ker (evalₐ J n).toRingHom := by
  rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
  intro b hb
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hb

include hf in
/-- One ideal containment supplies every ideal-power compatibility. -/
theorem power_le_kernel (n : ℕ) :
    I ^ n ≤ RingHom.ker (((evalₐ J n).restrictScalars R).comp f).toRingHom := by
  have h := (pow_le_pow_left' hf n).trans (pow_le_ker_eval J n)
  rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap] at h
  exact h

/-- Extend the original map using the proved power-filtration compatibility. -/
def extend : AdicCompletion I A →ₐ[R] AdicCompletion J B :=
  AdicFilteredAlgebraHom.extend I J f (power_le_kernel I J f hf)

/-- The constructed extension retains the original algebra map. -/
@[simp] theorem extend_of (a : A) :
    extend I J f hf (AdicCompletion.of I A a) = f a :=
  AdicFilteredAlgebraHom.extend_of I J f (power_le_kernel I J f hf) a

/-- The constructed extension retains the finite-order quotient maps. -/
theorem eval_extend (n : ℕ) (x : AdicCompletion I A) :
    evalₐ J n (extend I J f hf x) =
      AdicFilteredAlgebraHom.quotient I J f (power_le_kernel I J f hf) n (evalₐ I n x) :=
  AdicFilteredAlgebraHom.eval_extend I J f (power_le_kernel I J f hf) n x

end FLT.Mazur.AdicIdealFilteredMap
