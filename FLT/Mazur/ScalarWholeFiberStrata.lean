/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarConstructibleStrata

/-!
# Finite scalar strata whose entire fibers lie in a prescribed locus

Subtract the image of the complement from the actual scalar image. Chevalley
makes this difference constructible. The resulting finite scalar conditions
ensure both a nonempty fiber and containment of every full prime in the locus.
-/

@[expose] public noncomputable section
open Topology
namespace FLT.Mazur.ScalarConstructibleStrata
variable {R S : Type} [CommRing R] [CommRing S] (s : R →+* S)

/-- The nonempty whole-fiber condition is an exact difference of two actual images. -/
theorem whole_fiber_iff_image_difference (Z : Set (PrimeSpectrum S)) (P : PrimeSpectrum R) :
    ((∃ Q : PrimeSpectrum S, PrimeSpectrum.comap s Q = P) ∧
      ∀ Q : PrimeSpectrum S, PrimeSpectrum.comap s Q = P → Q ∈ Z) ↔
      P ∈ Set.range (PrimeSpectrum.comap s) \ (PrimeSpectrum.comap s '' Zᶜ) := by
  constructor
  · rintro ⟨hP, h⟩
    refine ⟨hP, ?_⟩
    rintro ⟨Q, hQ, he⟩
    exact hQ (h Q he)
  · rintro ⟨hP, h⟩
    refine ⟨hP, fun Q he ↦ ?_⟩
    by_contra hQ
    exact h ⟨Q, hQ, he⟩

/-- Finite equations cover exactly all nonempty scalar fibers contained in a constructible set. -/
theorem exists_whole_fiber_strata (hfp : s.FinitePresentation)
    (Z : Set (PrimeSpectrum S)) (hZ : IsConstructible Z) :
    ∃ pieces : Finset (R × Finset R), ∀ P : PrimeSpectrum R,
      (∃ a ∈ pieces, a.1 ∉ P.asIdeal ∧ ∀ r ∈ a.2, r ∈ P.asIdeal) ↔
      (∃ Q : PrimeSpectrum S, PrimeSpectrum.comap s Q = P) ∧
        ∀ Q : PrimeSpectrum S, PrimeSpectrum.comap s Q = P → Q ∈ Z := by
  obtain ⟨pieces, h⟩ := exists_finite_principal_strata _
    ((PrimeSpectrum.isConstructible_range_comap hfp).sdiff
      (PrimeSpectrum.isConstructible_comap_image hfp hZ.compl))
  exact ⟨pieces, fun P ↦ (h P).symm.trans (whole_fiber_iff_image_difference s Z P).symm⟩

/-- A finite family of closed equations has a constructible whole-fiber scalar locus. -/
theorem exists_whole_fiber_equation_strata (hfp : s.FinitePresentation) (T : Finset S) :
    ∃ pieces : Finset (R × Finset R), ∀ P : PrimeSpectrum R,
      (∃ a ∈ pieces, a.1 ∉ P.asIdeal ∧ ∀ r ∈ a.2, r ∈ P.asIdeal) ↔
      (∃ Q : PrimeSpectrum S, PrimeSpectrum.comap s Q = P) ∧
        ∀ Q : PrimeSpectrum S, PrimeSpectrum.comap s Q = P → ∀ t ∈ T, t ∈ Q.asIdeal := by
  have hT : IsConstructible (PrimeSpectrum.zeroLocus (T : Set S)) := by
    apply IsConstructible.of_compl
    exact (PrimeSpectrum.isRetrocompact_zeroLocus_compl T.finite_toSet).isConstructible
      (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
  exact exists_whole_fiber_strata s hfp (PrimeSpectrum.zeroLocus (T : Set S)) hT

end FLT.Mazur.ScalarConstructibleStrata
