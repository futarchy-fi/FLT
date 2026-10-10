/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationIteratedFiniteMaps

/-!
# Descending actual restrictions with their ambient path equations

A restriction in the original double open lifts to a finite double-open target.
All equations on finite-type ambient charts are imposed together while retaining
the old source rings and every specified map from those rings.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationIterated

universe u v w z w'

variable {R : Type u} [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P) (r : P) (s : Finset I)
  {ι : Type z} [Finite ι] (d : ι → FiniteRelationLocalization.Stage I r s)

/-- Actual original restrictions and their full ambient equations descend simultaneously. -/
theorem exists_restriction_paths (A : ι → Type w)
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Algebra.FinitePresentation R (A i)]
    (C : ι → Type w') [∀ i, CommRing (C i)] [∀ i, Algebra R (C i)]
    [∀ i, Algebra.FiniteType R (C i)] (t : Set.Ici s)
    (a : ∀ i, C i →ₐ[R] A i) (b : ∀ i, C i →ₐ[R] Stage R I r s (d i) t)
    (ρ : ∀ i, A i →ₐ[R] Quotient R I r s (d i))
    (hρ : ∀ i, (ρ i).comp (a i) = (toQuotient R I r s (d i) t).comp (b i)) :
    ∃ (q : Set.Ici s) (htq : t ≤ q),
      ∃ g : ∀ i, A i →ₐ[R] Stage R I r s (d i) q,
        (∀ i, (toQuotient R I r s (d i) q).comp (g i) = ρ i) ∧
        (∀ i, (g i).comp (a i) = (transition R I r s (d i) htq).comp (b i)) := by
  obtain ⟨q, htq, g, hg⟩ := exists_hom_lift_finite I r s d A t ρ
  have he (i) :
      (toQuotient R I r s (d i) q).comp ((g i).comp (a i)) =
      (toQuotient R I r s (d i) q).comp
        ((transition R I r s (d i) htq).comp (b i)) := by
    rw [← AlgHom.comp_assoc, hg, hρ, ← AlgHom.comp_assoc, toQuotient_comp]
  obtain ⟨k, hqk, hk⟩ := exists_hom_eq_finite I r s d C q
    (fun i ↦ (g i).comp (a i))
    (fun i ↦ (transition R I r s (d i) htq).comp (b i)) he
  refine ⟨k, htq.trans hqk,
    fun i ↦ (transition R I r s (d i) hqk).comp (g i), ?_, fun i ↦ ?_⟩
  · intro i
    rw [← AlgHom.comp_assoc, toQuotient_comp, hg]
  · rw [AlgHom.comp_assoc, hk, ← AlgHom.comp_assoc, transition_comp]

end FLT.Mazur.FiniteRelationIterated
