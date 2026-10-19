/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarClosedImageCoverage
public import FLT.Mazur.ScalarClosedGeometricLifts
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-!
# Principal scalar coverage along a prescribed closed branch

Constructibility gives a principal neighborhood along the specialization
closure of each prime in an image. Applied to closed affine equations, this
constructs actual scalar residue characters on that neighborhood. No claim
that the entire scalar specialization closure is covered is needed.
-/

@[expose] public noncomputable section
open Topology
namespace FLT.Mazur.ScalarClosedImageCoverage
variable {R S : Type} [CommRing R] [CommRing S]

/-- A constructible set contains a principal neighborhood along every one of its branches. -/
theorem exists_principal_specialization_subset (Z : Set (PrimeSpectrum R))
    (hZ : IsConstructible Z) (P : PrimeSpectrum R) (hP : P ∈ Z) :
    ∃ t : R, t ∉ P.asIdeal ∧ ∀ Q : PrimeSpectrum R,
      P.asIdeal ≤ Q.asIdeal → t ∉ Q.asIdeal → Q ∈ Z := by
  induction Z, hZ using IsConstructible.induction_of_isTopologicalBasis
      (fun t : R ↦ (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum R)))
      PrimeSpectrum.isTopologicalBasis_basic_opens
      (fun t ↦ PrimeSpectrum.isCompact_basicOpen t) with
  | sdiff t U hU =>
    refine ⟨t, hP.1, fun Q hPQ htQ ↦ ⟨htQ, ?_⟩⟩
    intro hQ
    have ho : IsOpen (⋃ j ∈ U, (PrimeSpectrum.basicOpen j : Set (PrimeSpectrum R))) :=
      isOpen_biUnion fun j _ ↦ (PrimeSpectrum.basicOpen j).isOpen
    exact hP.2 ((PrimeSpectrum.le_iff_specializes P Q).mp hPQ |>.mem_open ho hQ)
  | union Z hZ T hT ihZ ihT =>
    rcases hP with hP | hP
    · obtain ⟨t, ht, h⟩ := ihZ hP
      exact ⟨t, ht, fun Q hQ htQ ↦ Or.inl (h Q hQ htQ)⟩
    · obtain ⟨t, ht, h⟩ := ihT hP
      exact ⟨t, ht, fun Q hQ htQ ↦ Or.inr (h Q hQ htQ)⟩

variable (s : R →+* S) (J : Ideal S)

/-- Closed equations retain actual lifts on a constructed scalar principal branch. -/
theorem exists_closed_scalar_principal_branch
    (hfp : ((Ideal.Quotient.mk J).comp s).FinitePresentation)
    (P : PrimeSpectrum R) (hP : P.asIdeal ∈ (J.comap s).minimalPrimes) :
    ∃ t : R, t ∉ P.asIdeal ∧ ∀ Q : PrimeSpectrum R,
      P.asIdeal ≤ Q.asIdeal → t ∉ Q.asIdeal →
      ∃ w : S →+* AlgebraicClosure Q.asIdeal.ResidueField,
        w.comp s = algebraMap R _ ∧ ∀ b ∈ J, w b = 0 := by
  let π := Ideal.Quotient.mk J
  let g := π.comp s
  obtain ⟨q, hJ, hq⟩ := exists_prime_over_minimal_contraction s J P hP
  have hr : q ∈ Set.range (PrimeSpectrum.comap π) := by
    rw [range_comap_of_surjective _ π Ideal.Quotient.mk_surjective]
    simpa only [π, Ideal.mk_ker, PrimeSpectrum.mem_zeroLocus,
      SetLike.coe_subset_coe] using hJ
  obtain ⟨q', hq'⟩ := hr
  have hPg : P ∈ Set.range (PrimeSpectrum.comap g) := by
    refine ⟨q', ?_⟩
    change PrimeSpectrum.comap s (PrimeSpectrum.comap π q') = P
    rw [hq', hq]
  obtain ⟨t, ht, h⟩ := exists_principal_specialization_subset _
    (PrimeSpectrum.isConstructible_range_comap hfp) P hPg
  refine ⟨t, ht, fun Q hPQ htQ ↦ ?_⟩
  obtain ⟨qQ, hqQ⟩ := h Q hPQ htQ
  obtain ⟨v, hv, _⟩ := ScalarTestLocalization.exists_residue_geometric_failure g Q
    (RingHom.FiniteType.of_finitePresentation hfp) 1 qQ hqQ qQ.isPrime.one_notMem
  refine ⟨v.comp π, hv, fun b hb ↦ ?_⟩
  change v (Ideal.Quotient.mk J b) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero]

/-- Finite type suffices over a Noetherian original scalar ring. -/
theorem exists_closed_scalar_principal_branch_of_finiteType [IsNoetherianRing R]
    (hs : s.FiniteType) (P : PrimeSpectrum R)
    (hP : P.asIdeal ∈ (J.comap s).minimalPrimes) :
    ∃ t : R, t ∉ P.asIdeal ∧ ∀ Q : PrimeSpectrum R,
      P.asIdeal ≤ Q.asIdeal → t ∉ Q.asIdeal →
      ∃ w : S →+* AlgebraicClosure Q.asIdeal.ResidueField,
        w.comp s = algebraMap R _ ∧ ∀ b ∈ J, w b = 0 := by
  let g := (Ideal.Quotient.mk J).comp s
  have ht : g.FiniteType :=
    (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective).comp hs
  have hp : g.FinitePresentation := by
    let _ := g.toAlgebra
    exact Algebra.FinitePresentation.of_finiteType.mp ht
  exact exists_closed_scalar_principal_branch s J hp P hP

end FLT.Mazur.ScalarClosedImageCoverage
