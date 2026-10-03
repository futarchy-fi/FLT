/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveLineEndpoints
public import Mathlib.RingTheory.Polynomial.Quotient

/-!
# Covering the projective line by the torus and endpoints

The complement of the Laurent open consists of zero and infinity. The statement
covers all scheme points and does not require the coefficient field to be closed.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open scoped LaurentPolynomial
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.ProjectiveLine
variable (K : Type u) [Field K]
/-- The punctured affine line and its origin cover every scheme point. -/
theorem chart_torus_or_zero (z : chart K) :
    z ∈ Set.range (overlapLeft K) ∨ z ∈ Set.range (chartZero K) := by
  rw [show Set.range (overlapLeft K) =
    (PrimeSpectrum.basicOpen (X : K[X]) : Set (PrimeSpectrum K[X])) from
    PrimeSpectrum.localization_away_comap_range K[T;T⁻¹] X]
  have he : Set.range (chartZero K) = PrimeSpectrum.zeroLocus ({X} : Set K[X]) := by
    change Set.range (PrimeSpectrum.comap (evalRingHom (0 : K))) = _
    rw [range_comap_of_surjective K _ (fun a ↦ ⟨C a, by simp⟩),
      ker_evalRingHom, C_0, sub_zero, PrimeSpectrum.zeroLocus_span]
  rw [he]
  change X ∉ z.asIdeal ∨ ({X} : Set K[X]) ⊆ z.asIdeal
  simp only [Set.singleton_subset_iff]
  exact (Classical.em _).symm

/-- The Laurent open and the two rational endpoints cover the projective line. -/
theorem torus_or_endpoints (z : scheme K) :
    z ∈ Set.range (overlapLeft K ≫ left K) ∨
    z ∈ Set.range (zero K) ∨ z ∈ Set.range (infinity K) := by
  rcases charts_cover K z with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rcases chart_torus_or_zero K a with ⟨t, rfl⟩ | ⟨x, rfl⟩
    · exact Or.inl ⟨t, rfl⟩
    · exact Or.inr (Or.inl ⟨x, rfl⟩)
  · rcases chart_torus_or_zero K a with ⟨t, rfl⟩ | ⟨x, rfl⟩
    · left
      refine ⟨(inversion K).inv t, ?_⟩
      have he := congrArg (fun f ↦ (inversion K).inv ≫ f) (overlap_condition K)
      simp only [overlapRight, Category.assoc, Iso.inv_hom_id_assoc] at he
      exact congrArg (fun f ↦ f t) he
    · exact Or.inr (Or.inr ⟨x, rfl⟩)
end FLT.Mazur.ProjectiveLine
