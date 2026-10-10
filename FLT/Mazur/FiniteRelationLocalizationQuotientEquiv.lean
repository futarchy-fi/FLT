/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationLocalizationExactIdeals
public import FLT.Mazur.SurjectiveAlgHomKernelEquiv

/-!
# Finitely presented quotients are later principal-open stages

A surjection onto a finitely presented algebra whose kernel dies in the full
quotient is realized by an actual isomorphism from a later localized stage.
This uses equality of kernels, not eventual round-trip equalities.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationLocalization

universe u v w

variable {R : Type u} [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  [Algebra.FinitePresentation R P] (I : Ideal P) (r : P)
  {A : Type w} [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A]

/-- A finite quotient compatible with the limit is exactly a later principal-open stage. -/
theorem exists_quotient_equiv (s : Finset I) (f : Stage I r s →ₐ[R] A)
    (hf : Function.Surjective f)
    (h : RingHom.ker f.toRingHom ≤ RingHom.ker (toQuotient R I r s).toRingHom) :
    ∃ (t : Finset I) (hst : s ≤ t) (e : Stage I r t ≃ₐ[R] A),
      e.toAlgHom.comp (transition R I r hst) = f := by
  obtain ⟨t, hst, he⟩ := exists_transition_ker_eq R I r s (RingHom.ker f.toRingHom)
    (Algebra.FinitePresentation.ker_fG_of_surjective f hf) h
  obtain ⟨e, he⟩ := exists_algEquiv_of_ker_eq (transition R I r hst) f
    (transition_surjective R I r hst) hf he
  exact ⟨t, hst, e, he⟩

end FLT.Mazur.FiniteRelationLocalization
