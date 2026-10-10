/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Compatible isomorphisms from equal kernels

Two surjective algebra maps with the same kernel identify their targets, with
the identification commuting with the original maps.
-/

@[expose] public noncomputable section

namespace FLT.Mazur

universe u v w z

variable {R : Type u} [CommRing R]
  {P : Type v} [CommRing P] [Algebra R P]
  {A : Type w} [CommRing A] [Algebra R A]
  {B : Type z} [CommRing B] [Algebra R B]

/-- Equal kernels of surjections give a compatible algebra isomorphism of their targets. -/
theorem exists_algEquiv_of_ker_eq (f : P →ₐ[R] A) (g : P →ₐ[R] B)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : RingHom.ker f = RingHom.ker g) :
    ∃ e : A ≃ₐ[R] B, e.toAlgHom.comp f = g := by
  let e := (Ideal.quotientKerAlgEquivOfSurjective hf).symm.trans
    ((Ideal.quotientEquivAlgOfEq R h).trans (Ideal.quotientKerAlgEquivOfSurjective hg))
  refine ⟨e, ?_⟩
  apply AlgHom.ext
  intro x
  change Ideal.quotientKerAlgEquivOfSurjective hg
    (Ideal.quotientEquivAlgOfEq R h
      ((Ideal.quotientKerAlgEquivOfSurjective hf).symm (f x))) = g x
  rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_mk]

end FLT.Mazur
