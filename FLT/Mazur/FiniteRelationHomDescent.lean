/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationDetection

/-!
# Maps from finitely presented algebras descend to finite relation stages

Lift polynomial generators first, then impose the finitely many source
relations at one later stage. The descended map and its compatibility are
constructed, rather than included as assumptions of an approximation record.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationModel

universe u v w z

variable {R : Type u} [CommRing R]

/-- A map from a polynomial algebra lifts through any surjective algebra map. -/
theorem exists_polynomial_lift {A : Type v} [CommRing A] [Algebra R A]
    {B : Type w} [CommRing B] [Algebra R B] {ι : Type z}
    (q : A →ₐ[R] B) (hq : Function.Surjective q) (f : MvPolynomial ι R →ₐ[R] B) :
    ∃ g : MvPolynomial ι R →ₐ[R] A, q.comp g = f := by
  classical
  choose x hx using fun i ↦ hq (f (MvPolynomial.X i))
  refine ⟨MvPolynomial.aeval x, ?_⟩
  ext i
  simpa using hx i

variable {P : Type v} [CommRing P] [Algebra R P] (I : Ideal P)

/-- Finitely many elements killed by the quotient are killed at one later stage. -/
theorem exists_transition_kills {ι : Type z} [Finite ι] (s : Finset I)
    (x : ι → Stage I s) (h : ∀ i, toQuotient R I s (x i) = 0) :
    ∃ (t : Finset I) (hst : s ≤ t), ∀ i, transition R I hst (x i) = 0 := by
  obtain ⟨t, hst, ht⟩ := exists_transition_eq_finite R I s x (fun _ ↦ 0)
    (fun i ↦ (h i).trans (map_zero _).symm)
  exact ⟨t, hst, fun i ↦ (ht i).trans (map_zero _)⟩

/-- A finitely generated ideal killed in the quotient is killed at a finite stage. -/
theorem exists_transition_kills_ideal {A : Type w} [CommRing A] [Algebra R A]
    (J : Ideal A) (hJ : J.FG) (s : Finset I) (g : A →ₐ[R] Stage I s)
    (hg : J ≤ RingHom.ker ((toQuotient R I s).comp g).toRingHom) :
    ∃ (t : Finset I) (hst : s ≤ t),
      J ≤ RingHom.ker ((transition R I hst).comp g).toRingHom := by
  classical
  obtain ⟨a, ha⟩ := hJ
  obtain ⟨t, hst, ht⟩ := exists_transition_kills (R := R) I s (fun i : a ↦ g i.val)
    (fun i ↦ hg (ha ▸ Submodule.subset_span i.property))
  refine ⟨t, hst, ?_⟩
  rw [← ha]
  apply Submodule.span_le.mpr
  intro x hx
  exact ht ⟨x, hx⟩

/-- Any map from a finitely presented algebra factors through a later relation stage. -/
theorem exists_hom_lift {A : Type w} [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] (s : Finset I) (f : A →ₐ[R] P ⧸ I) :
    ∃ (t : Finset I), s ≤ t ∧ ∃ g : A →ₐ[R] Stage I t,
      (toQuotient R I t).comp g = f := by
  obtain ⟨n, q, hq, hker⟩ := Algebra.FinitePresentation.out (R := R) (A := A)
  obtain ⟨g, hg⟩ := exists_polynomial_lift (toQuotient R I s)
    (toQuotient_surjective R I s) (f.comp q)
  have hk : RingHom.ker q.toRingHom ≤
      RingHom.ker ((toQuotient R I s).comp g).toRingHom := by
    rw [hg]
    intro x hx
    change f (q x) = 0
    change q x = 0 at hx
    rw [hx, map_zero]
  obtain ⟨t, hst, ht⟩ := exists_transition_kills_ideal I _ hker s g hk
  refine ⟨t, hst, q.liftOfSurjective hq ((transition R I hst).comp g) ht, ?_⟩
  apply AlgHom.ext
  intro a
  obtain ⟨x, rfl⟩ := hq a
  rw [AlgHom.comp_apply, AlgHom.liftOfSurjective_apply]
  change toQuotient R I t (transition R I hst (g x)) = f (q x)
  rw [← AlgHom.comp_apply, toQuotient_comp]
  exact AlgHom.congr_fun hg x

end FLT.Mazur.FiniteRelationModel
