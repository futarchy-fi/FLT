/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-!
# Finite scalar equations for constructible spectral sets

Every constructible scalar set is a finite union of pieces specified by one
nonvanishing denominator and finitely many vanishing equations. This describes
all boundary pieces as well as the initial dense principal branches.
-/

@[expose] public noncomputable section
open Topology
namespace FLT.Mazur.ScalarConstructibleStrata
variable {R : Type} [CommRing R]

/-- A finite list of scalar equations and inequations describes the entire constructible set. -/
theorem exists_finite_principal_strata (Z : Set (PrimeSpectrum R))
    (hZ : IsConstructible Z) :
    ∃ pieces : Finset (R × Finset R), ∀ P : PrimeSpectrum R,
      P ∈ Z ↔ ∃ a ∈ pieces, a.1 ∉ P.asIdeal ∧ ∀ r ∈ a.2, r ∈ P.asIdeal := by
  classical
  induction Z, hZ using IsConstructible.induction_of_isTopologicalBasis
      (fun t : R ↦ (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum R)))
      PrimeSpectrum.isTopologicalBasis_basic_opens
      (fun t ↦ PrimeSpectrum.isCompact_basicOpen t) with
  | sdiff t U hU =>
    refine ⟨{(t, hU.toFinset)}, fun P ↦ ?_⟩
    simp only [Set.mem_sdiff, Set.mem_iUnion, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen,
      Finset.mem_singleton, exists_eq_left, Set.Finite.mem_toFinset,
      not_exists, not_not]
  | union Z hZ T hT ihZ ihT =>
    obtain ⟨a, ha⟩ := ihZ
    obtain ⟨b, hb⟩ := ihT
    refine ⟨a ∪ b, fun P ↦ ?_⟩
    simp only [Set.mem_union, ha, hb, Finset.mem_union]
    constructor
    · rintro (⟨s, hs, h⟩ | ⟨s, hs, h⟩)
      · exact ⟨s, Or.inl hs, h⟩
      · exact ⟨s, Or.inr hs, h⟩
    · rintro ⟨s, hs | hs, h⟩
      · exact Or.inl ⟨s, hs, h⟩
      · exact Or.inr ⟨s, hs, h⟩

/-- Each piece is the intersection of a principal open with a finitely defined closed set. -/
theorem stratum_iff_span_le (a : R × Finset R) (P : PrimeSpectrum R) :
    (a.1 ∉ P.asIdeal ∧ ∀ r ∈ a.2, r ∈ P.asIdeal) ↔
      a.1 ∉ P.asIdeal ∧ Ideal.span (a.2 : Set R) ≤ P.asIdeal := by
  rw [Ideal.span_le]
  rfl

end FLT.Mazur.ScalarConstructibleStrata
