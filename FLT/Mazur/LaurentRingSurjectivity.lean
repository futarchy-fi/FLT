/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Polynomial.Laurent

/-!
# Surjectivity onto a Laurent polynomial ring

Constants, T, and a perturbation T⁻¹ + c T² generate the Laurent ring. This
criterion keeps the source ring arbitrary so it applies to actual chart maps.
-/

open scoped LaurentPolynomial
@[expose] public noncomputable section
namespace FLT.Mazur
open LaurentPolynomial
variable {R A : Type*} [CommRing R] [CommRing A]

/-- A ring map whose image contains constants and both Laurent generators is surjective. -/
theorem laurent_surjective_of_generators (f : A →+* R[T;T⁻¹])
    (hC : ∀ r, C r ∈ f.range) (hT : T 1 ∈ f.range) (hI : T (-1) ∈ f.range) :
    Function.Surjective f := by
  intro p
  change p ∈ f.range
  induction p using LaurentPolynomial.induction_on with
  | h_C r => exact hC r
  | h_add hp hq => exact f.range.add_mem hp hq
  | h_C_mul_T n r ih =>
      simpa only [T_add, ← mul_assoc] using f.range.mul_mem ih hT
  | h_C_mul_T_Z n r ih =>
      simpa only [sub_eq_add_neg, T_add, ← mul_assoc] using f.range.mul_mem ih hI

/-- A quadratic perturbation of the inverse coordinate suffices for surjectivity. -/
theorem laurent_surjective_of_perturbed_inverse (f : A →+* R[T;T⁻¹]) (c : R)
    (hC : ∀ r, C r ∈ f.range) (hT : T 1 ∈ f.range)
    (hI : T (-1) + C c * T 2 ∈ f.range) : Function.Surjective f := by
  apply laurent_surjective_of_generators f hC hT
  have h2 : T 2 ∈ f.range := by
    simpa only [← T_add, Int.reduceAdd] using f.range.mul_mem hT hT
  simpa only [add_sub_cancel_right] using f.range.sub_mem hI (f.range.mul_mem (hC c) h2)

end FLT.Mazur
