/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationIteratedFiniteMaps

/-!
# Descending restrictions through prescribed source quotients

A finite restriction can be retained after any prescribed finitely presented
source quotient compatible with its original map. The finite kernel is killed
at a later target stage, and all old squares remain exact. This does not assert
that source and target refinements can be made at the same stage in a cyclic diagram.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationIterated

universe u v w z w'

variable {R : Type u} [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P) (r : P) (s : Finset I) (d : FiniteRelationLocalization.Stage I r s)

/-- A specified source quotient admits a compatible finite restriction after target refinement. -/
theorem exists_source_quotient_lift {A : Type w} [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] {B : Type w'} [CommRing B] [Algebra R B]
    [Algebra.FinitePresentation R B] (π : A →ₐ[R] B) (hπ : Function.Surjective π)
    (t : Set.Ici s) (g : A →ₐ[R] Stage R I r s d t) (f : B →ₐ[R] Quotient R I r s d)
    (h : (toQuotient R I r s d t).comp g = f.comp π) :
    ∃ (q : Set.Ici s) (htq : t ≤ q) (k : B →ₐ[R] Stage R I r s d q),
      k.comp π = (transition R I r s d htq).comp g ∧
      (toQuotient R I r s d q).comp k = f := by
  have hk : RingHom.ker π.toRingHom ≤
      RingHom.ker ((toQuotient R I r s d t).comp g).toRingHom := by
    rw [h]
    intro x hx
    change f (π x) = 0
    change π x = 0 at hx
    rw [hx, map_zero]
  obtain ⟨q, htq, hq⟩ := exists_transition_kills_ideal I r s d (RingHom.ker π.toRingHom)
    (Algebra.FinitePresentation.ker_fG_of_surjective π hπ) t g hk
  let k := π.liftOfSurjective hπ ((transition R I r s d htq).comp g) hq
  have he : k.comp π = (transition R I r s d htq).comp g := by
    apply AlgHom.ext
    intro x
    exact AlgHom.liftOfSurjective_apply π hπ _ hq x
  refine ⟨q, htq, k, he, ?_⟩
  apply (AlgHom.cancel_right hπ).mp
  rw [AlgHom.comp_assoc, he, ← AlgHom.comp_assoc, toQuotient_comp, h]

variable {ι : Type z} [Finite ι]

/-- All prescribed source quotients can be imposed while retaining a single shared target stage. -/
theorem exists_source_quotient_lift_finite
    (d : ι → FiniteRelationLocalization.Stage I r s)
    (A : ι → Type w) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Algebra.FinitePresentation R (A i)]
    (B : ι → Type w') [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    [∀ i, Algebra.FinitePresentation R (B i)]
    (π : ∀ i, A i →ₐ[R] B i) (hπ : ∀ i, Function.Surjective (π i)) (t : Set.Ici s)
    (g : ∀ i, A i →ₐ[R] Stage R I r s (d i) t)
    (f : ∀ i, B i →ₐ[R] Quotient R I r s (d i))
    (h : ∀ i, (toQuotient R I r s (d i) t).comp (g i) = (f i).comp (π i)) :
    ∃ (q : Set.Ici s) (htq : t ≤ q),
      ∃ k : ∀ i, B i →ₐ[R] Stage R I r s (d i) q,
        (∀ i, (k i).comp (π i) = (transition R I r s (d i) htq).comp (g i)) ∧
        (∀ i, (toQuotient R I r s (d i) q).comp (k i) = f i) := by
  choose q hq k hk hf using fun i ↦
    exists_source_quotient_lift I r s (d i) (π i) (hπ i) t (g i) (f i) (h i)
  obtain ⟨z, htz, hqz⟩ := exists_common_stage I s t q
  refine ⟨z, htz, fun i ↦ (transition R I r s (d i) (hqz i)).comp (k i),
    fun i ↦ ?_, fun i ↦ ?_⟩
  · rw [AlgHom.comp_assoc, hk, ← AlgHom.comp_assoc, transition_comp]
  · rw [← AlgHom.comp_assoc, toQuotient_comp, hf]

end FLT.Mazur.FiniteRelationIterated
