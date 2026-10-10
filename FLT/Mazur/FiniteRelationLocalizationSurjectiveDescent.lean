/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationLocalizationFiniteDetection
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Surjectivity at localized finite relation stages

If a map onto the limiting quotient is surjective, lift preimages of a finite
set of target generators and impose their equalities. A map inducing an
isomorphism with the full quotient is consequently an isomorphism at a later
stage. Localization introduces no finite-presentation hypothesis on the
limiting quotient.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationLocalization

universe u v w

variable {R : Type u} [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P) (r : P)
  {A : Type w} [CommRing A] [Algebra R A]

/-- Surjectivity onto the full quotient is realized after finitely many relations. -/
theorem exists_surjective_stage [Algebra.FiniteType R P] (s : Finset I) (f : A →ₐ[R] Stage I r s)
    (hf : Function.Surjective ((toQuotient R I r s).comp f)) :
    ∃ (t : Finset I) (hst : s ≤ t), Function.Surjective ((transition R I r hst).comp f) := by
  classical
  obtain ⟨n, q, hq⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R (Stage I r s))
  choose a ha using fun i : Fin n ↦ hf (toQuotient R I r s (q (MvPolynomial.X i)))
  obtain ⟨t, hst, ht⟩ := exists_transition_eq_finite R I r s
    (fun i ↦ f (a i)) (fun i ↦ q (MvPolynomial.X i)) ha
  refine ⟨t, hst, ?_⟩
  have he : ((transition R I r hst).comp f).comp (MvPolynomial.aeval a) =
      (transition R I r hst).comp q := by
    ext i
    simpa using ht i
  apply Function.Surjective.of_comp
    (g := (MvPolynomial.aeval a : MvPolynomial (Fin n) R →ₐ[R] A))
  change Function.Surjective (((transition R I r hst).comp f).comp (MvPolynomial.aeval a))
  rw [he]
  exact (transition_surjective R I r hst).comp hq

/-- Injectivity at the limit already implies injectivity at every larger stage. -/
theorem transition_comp_injective {s t : Finset I} (hst : s ≤ t)
    (f : A →ₐ[R] Stage I r s) (hf : Function.Injective ((toQuotient R I r s).comp f)) :
    Function.Injective ((transition R I r hst).comp f) := by
  intro x y h
  apply hf
  have he := congrArg (toQuotient R I r t) h
  change ((toQuotient R I r t).comp (transition R I r hst)) (f x) =
    ((toQuotient R I r t).comp (transition R I r hst)) (f y) at he
  rwa [toQuotient_comp] at he

/-- A map inducing an isomorphism with the quotient is an isomorphism at a finite stage. -/
theorem exists_bijective_stage [Algebra.FiniteType R P] (s : Finset I) (f : A →ₐ[R] Stage I r s)
    (hf : Function.Bijective ((toQuotient R I r s).comp f)) :
    ∃ (t : Finset I) (hst : s ≤ t), Function.Bijective ((transition R I r hst).comp f) := by
  obtain ⟨t, hst, ht⟩ := exists_surjective_stage I r s f hf.2
  exact ⟨t, hst, transition_comp_injective I r hst f hf.1, ht⟩

end FLT.Mazur.FiniteRelationLocalization
