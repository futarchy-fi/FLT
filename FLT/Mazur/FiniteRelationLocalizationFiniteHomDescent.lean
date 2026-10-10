/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationLocalizationHomDescent
public import FLT.Mazur.FiniteRelationLocalizationHomEquality

/-!
# Simultaneous maps and relations into principal-open models

Finite families with different sources descend to one localized stage.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationLocalization

universe u v w z

variable {R : Type u} [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P) (d : P)

/-- Finitely many finitely presented sources have lifts into one common stage. -/
theorem exists_hom_lift_finite {ι : Type z} [Finite ι]
    (A : ι → Type w) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Algebra.FinitePresentation R (A i)] (s : Finset I)
    (f : ∀ i, A i →ₐ[R] Quotient I d) :
    ∃ t : Finset I, s ≤ t ∧ ∃ g : ∀ i, A i →ₐ[R] Stage I d t,
      ∀ i, (toQuotient R I d t).comp (g i) = f i := by
  classical
  let _ := Fintype.ofFinite ι
  choose t ht g hg using fun i ↦ exists_hom_lift I d s (f i)
  let q := s ∪ Finset.univ.biUnion t
  have hsq : s ≤ q := Finset.subset_union_left
  have htq (i) : t i ≤ q := by
    intro x hx
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩)
  refine ⟨q, hsq, fun i ↦ (transition R I d (htq i)).comp (g i), fun i ↦ ?_⟩
  rw [← AlgHom.comp_assoc, toQuotient_comp, hg]

/-- Finite equations between composites can be imposed on an already lifted family. -/
theorem exists_hom_relations {ι : Type w} {κ : Type z} [Finite κ]
    (A : ι → Type v) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    (C : κ → Type w) [∀ k, CommRing (C k)] [∀ k, Algebra R (C k)]
    [∀ k, Algebra.FiniteType R (C k)] (l r : κ → ι)
    (a : ∀ k, C k →ₐ[R] A (l k)) (b : ∀ k, C k →ₐ[R] A (r k))
    (s : Finset I) (g : ∀ i, A i →ₐ[R] Stage I d s)
    (h : ∀ k, (toQuotient R I d s).comp ((g (l k)).comp (a k)) =
      (toQuotient R I d s).comp ((g (r k)).comp (b k))) :
    ∃ (t : Finset I) (hst : s ≤ t),
      ∀ k, ((transition R I d hst).comp (g (l k))).comp (a k) =
        ((transition R I d hst).comp (g (r k))).comp (b k) := by
  obtain ⟨t, hst, ht⟩ := exists_transition_hom_eq_finite I d C s
    (fun k ↦ (g (l k)).comp (a k)) (fun k ↦ (g (r k)).comp (b k)) h
  exact ⟨t, hst, fun k ↦ by simpa only [AlgHom.comp_assoc] using ht k⟩

end FLT.Mazur.FiniteRelationLocalization
