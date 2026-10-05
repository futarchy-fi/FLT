/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePresentationIntegerModel

/-!
# Common upper bounds for finite coefficient stages

Finitely many finite-type integer subalgebras fit in one finite-type stage.
The construction also includes a prescribed finite set of coefficients.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.Approximation

universe u v

/-- Finite coefficient stages admit a finite-type common upper bound. -/
theorem exists_common_coefficient_stage {A : Type u} [CommRing A]
    {I : Type v} [Finite I] (R : I → Subalgebra ℤ A)
    (hR : ∀ i, Algebra.FiniteType ℤ (R i)) (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧ ∀ i, R i ≤ S := by
  classical
  have hfg (i) : ∃ t : Finset A, Algebra.adjoin ℤ (t : Set A) = R i :=
    (R i).fg_iff_finiteType.mpr (hR i)
  choose t ht using hfg
  let U : Set A := s ∪ ⋃ i, (t i : Set A)
  have hU : U.Finite := hs.union (Set.finite_iUnion fun i ↦ (t i).finite_toSet)
  refine ⟨Algebra.adjoin ℤ U, Algebra.FiniteType.adjoin_of_finite hU,
    fun a ha ↦ Algebra.subset_adjoin (Or.inl ha), fun i ↦ ?_⟩
  rw [← ht i, Algebra.adjoin_le_iff]
  intro a ha
  exact Algebra.subset_adjoin (Or.inr (Set.mem_iUnion.mpr ⟨i, ha⟩))

/-- A common stage can retain an initial stage even when the family is empty. -/
theorem exists_common_coefficient_extension {A : Type u} [CommRing A]
    {I : Type v} [Finite I] (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀]
    (R : I → Subalgebra ℤ A) (hR : ∀ i, Algebra.FiniteType ℤ (R i))
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      A₀ ≤ S ∧ ∀ i, R i ≤ S := by
  let T : Option I → Subalgebra ℤ A := Option.elim' A₀ R
  have hT : ∀ i, Algebra.FiniteType ℤ (T i)
    | none => by change Algebra.FiniteType ℤ A₀; infer_instance
    | some i => hR i
  obtain ⟨S, hS, hsS, hle⟩ := exists_common_coefficient_stage T hT s hs
  exact ⟨S, hS, hsS, hle none, fun i ↦ hle (some i)⟩

end FLT.Mazur.Approximation
