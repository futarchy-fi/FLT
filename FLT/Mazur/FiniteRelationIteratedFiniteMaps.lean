/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationIteratedHomDescent

/-!
# Shared relation stages for different double opens

Different second denominators retain one common relation stage. This allows
all incoming restriction maps at an overlap chart to descend simultaneously.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationIterated

universe u v w z

variable {R : Type u} [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P) (r : P) (s : Finset I)
  {ι : Type z} [Finite ι] (d : ι → FiniteRelationLocalization.Stage I r s)

/-- Finitely many later relation stages have a common upper bound above the initial stage. -/
theorem exists_common_stage (t : Set.Ici s) (q : ι → Set.Ici s) :
    ∃ k : Set.Ici s, t ≤ k ∧ ∀ i, q i ≤ k := by
  classical
  let _ := Fintype.ofFinite ι
  refine ⟨⟨t.val ∪ Finset.univ.biUnion (fun i ↦ (q i).val),
    t.property.trans Finset.subset_union_left⟩, Finset.subset_union_left, fun i z hz ↦ ?_⟩
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hz⟩)

/-- Maps into different double opens descend while sharing their ambient relation stage. -/
theorem exists_hom_lift_finite (A : ι → Type w)
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Algebra.FinitePresentation R (A i)] (t : Set.Ici s)
    (f : ∀ i, A i →ₐ[R] Quotient R I r s (d i)) :
    ∃ q : Set.Ici s, t ≤ q ∧ ∃ g : ∀ i, A i →ₐ[R] Stage R I r s (d i) q,
      ∀ i, (toQuotient R I r s (d i) q).comp (g i) = f i := by
  choose q hq g hg using fun i ↦ exists_hom_lift I r s (d i) t (f i)
  obtain ⟨k, htk, hqk⟩ := exists_common_stage I s t q
  refine ⟨k, htk, fun i ↦ (transition R I r s (d i) (hqk i)).comp (g i), fun i ↦ ?_⟩
  rw [← AlgHom.comp_assoc, toQuotient_comp, hg]

/-- Full-ring map equalities on different double opens hold at one shared later stage. -/
theorem exists_hom_eq_finite (A : ι → Type w)
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Algebra.FiniteType R (A i)] (t : Set.Ici s)
    (f g : ∀ i, A i →ₐ[R] Stage R I r s (d i) t)
    (h : ∀ i, (toQuotient R I r s (d i) t).comp (f i) =
      (toQuotient R I r s (d i) t).comp (g i)) :
    ∃ (q : Set.Ici s) (htq : t ≤ q),
      ∀ i, (transition R I r s (d i) htq).comp (f i) =
        (transition R I r s (d i) htq).comp (g i) := by
  choose q hq he using fun i ↦ exists_transition_hom_eq I r s (d i) t (f i) (g i) (h i)
  obtain ⟨k, htk, hqk⟩ := exists_common_stage I s t q
  refine ⟨k, htk, fun i ↦ ?_⟩
  rw [← transition_comp R I r s (d i) (hq i) (hqk i), AlgHom.comp_assoc, he,
    ← AlgHom.comp_assoc, transition_comp]

end FLT.Mazur.FiniteRelationIterated
