/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceCofinalBijections
public import FLT.Mazur.FiniteRelationIteratedEquationPersistence

/-!
# Local equations at one bijective occurrence refinement

Finite families of full-ring equalities may live on different principal
subopens of each overlap. Equality on the original subopens is detected
at one occurrence refinement with bijective coordinates and arbitrary
ambient relation lower bounds.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

attribute [local irreducible] principalQuotientEquiv
  FiniteRelationIterated.toQuotient FiniteRelationLocalization.toQuotient
  FiniteRelationIterated.transition FiniteRelationLocalization.transition

universe u v w z z' 

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  [Finite ι] [∀ i, Finite (J i)]
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))

variable [Finite κ]

variable (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))

/-- The principal subopen ring with its denominator fixed at an earlier overlap stage. -/
abbrev principalOccurrenceLocalStage (j : κ)
    (d : PrincipalStage R (B j) (b j) (x.target j)) (t : Set.Ici (x.target j)) :=
  FiniteRelationIterated.Stage R (relationIdeal R (B j))
    (principalRepresentative R (B j) (b j)) (x.target j) d t

/-- Refine all local equations at once while retaining bijective occurrence coordinates. -/
theorem exists_principalOccurrence_local_equations
    {ν : κ → Type z'} [∀ j, Finite (ν j)]
    (d : ∀ j, ν j → PrincipalStage R (B j) (b j) (x.target j))
    (T : ∀ j, ν j → Type u) [∀ j n, CommRing (T j n)] [∀ j n, Algebra R (T j n)]
    [∀ j n, Algebra.FiniteType R (T j n)]
    (t : ∀ j, Set.Ici (x.target j))
    (l r : ∀ j n, T j n →ₐ[R] principalOccurrenceLocalStage e x j (d j n) (t j))
    (h : ∀ j n,
      (FiniteRelationIterated.toQuotient R (relationIdeal R (B j))
        (principalRepresentative R (B j) (b j)) (x.target j) (d j n) (t j)).comp (l j n) =
      (FiniteRelationIterated.toQuotient R (relationIdeal R (B j))
        (principalRepresentative R (B j) (b j)) (x.target j) (d j n) (t j)).comp (r j n))
    (s : ∀ i, Finset (relationIdeal R (A i))) :
    ∃ y : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom),
      ∃ hxy : x ≤ y, s ≤ y.source ∧ (∀ i k, Function.Bijective (y.hom i k)) ∧
        ∃ ht : ∀ j, (t j).val ≤ y.target j, ∀ j n,
          (FiniteRelationIterated.transition R (relationIdeal R (B j))
            (principalRepresentative R (B j) (b j)) (x.target j) (d j n)
            (show t j ≤ ⟨y.target j, principalOccurrence_target_mono hxy j⟩ from ht j)).comp
              (l j n) =
          (FiniteRelationIterated.transition R (relationIdeal R (B j))
            (principalRepresentative R (B j) (b j)) (x.target j) (d j n)
            (show t j ≤ ⟨y.target j, principalOccurrence_target_mono hxy j⟩ from ht j)).comp
              (r j n) := by
  choose q htq he using fun j ↦ FiniteRelationIterated.exists_hom_eq_finite
    (relationIdeal R (B j)) (principalRepresentative R (B j) (b j)) (x.target j)
    (d j) (T j) (t j) (l j) (r j) (h j)
  obtain ⟨y, hxy, hs, hq, hy⟩ :=
    exists_principalOccurrence_bijective_refinement e x s (fun j ↦ (q j).val)
  refine ⟨y, hxy, hs, hy,
    fun j ↦ (show (t j).val ≤ (q j).val from htq j).trans (hq j), fun j n ↦ ?_⟩
  have hqn : q j ≤ ⟨y.target j, principalOccurrence_target_mono hxy j⟩ := hq j
  exact FiniteRelationIterated.hom_eq_of_le R (relationIdeal R (B j))
    (principalRepresentative R (B j) (b j)) (x.target j) (d j n)
    (htq j) hqn (l j n) (r j n) (he j n)

end FLT.Mazur.FiniteTypeRelationModel
