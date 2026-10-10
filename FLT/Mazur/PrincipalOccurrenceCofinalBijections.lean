/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceSurjectiveBijections

/-!
# Unconditional cofinal bijective occurrence refinements

Finite restrictions and simultaneous diagram refinement supply the full
ambient paths needed for kernel patching. All target labels remain shared.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  [Finite ι] [∀ i, Finite (J i)]
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))

variable [Finite κ]

/-- Any occurrence stage has a bijective refinement above arbitrary relation bounds. -/
theorem exists_principalOccurrence_bijective_refinement
    (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))
    (s : ∀ i, Finset (relationIdeal R (A i)))
    (t : ∀ j, Finset (relationIdeal R (B j))) :
    ∃ y : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom),
      x ≤ y ∧ s ≤ y.source ∧ t ≤ y.target ∧
        ∀ i k, Function.Bijective (y.hom i k) := by
  obtain ⟨z, hxz, _hs, hz⟩ :=
    exists_principalOccurrence_surjective (fun i k ↦ (e i k).surjective) x
  obtain ⟨y, hzy, hs, ht, hy⟩ :=
    exists_principalOccurrence_bijective_of_surjective e z hz s t
  exact ⟨y, hxz.trans hzy, hs, ht, hy⟩

/-- Simultaneous bijective coordinates exist above every source and overlap relation bound. -/
theorem exists_principalOccurrence_bijective_stage
    (s : ∀ i, Finset (relationIdeal R (A i)))
    (t : ∀ j, Finset (relationIdeal R (B j))) :
    ∃ x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom),
      s ≤ x.source ∧ t ≤ x.target ∧ ∀ i k, Function.Bijective (x.hom i k) := by
  obtain ⟨x, _hs, _ht⟩ :=
    exists_principalOccurrenceStage (fun i k ↦ (e i k).toAlgHom) s t
  obtain ⟨y, _hxy, hs, ht, hy⟩ := exists_principalOccurrence_bijective_refinement e x s t
  exact ⟨y, hs, ht, hy⟩

end FLT.Mazur.FiniteTypeRelationModel
