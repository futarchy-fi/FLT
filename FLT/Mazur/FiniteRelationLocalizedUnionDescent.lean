/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationLocalizationDetection
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Descent of inclusions in finite unions of principal opens

A power-membership certificate for a finite ideal span descends through the
localized relation system. This also handles covers of proper open subsets.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationLocalization

universe u v w

/-- Inclusion in a union of principal opens is radical membership in their generated ideal. -/
theorem basicOpen_le_iSup_iff {S : Type*} [CommRing S] {ι : Type*}
    (a : S) (b : ι → S) :
    PrimeSpectrum.basicOpen a ≤ ⨆ i, PrimeSpectrum.basicOpen (b i) ↔
      a ∈ (Ideal.span (Set.range b)).radical := by
  rw [← SetLike.coe_subset_coe, TopologicalSpace.Opens.coe_iSup]
  simp only [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, ← Set.compl_iInter,
    ← PrimeSpectrum.zeroLocus_iUnion, Set.iUnion_singleton_eq_range, Set.compl_subset_compl]
  rw [← PrimeSpectrum.zeroLocus_span (Set.range b),
    ← PrimeSpectrum.zeroLocus_span {a}, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff,
    Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]

variable {R : Type u} [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P) (r : P)

/-- A finite union inclusion in the localized quotient persists on a relation tail. -/
theorem exists_localized_principal_union_inclusion_tail {ι : Type w} [Finite ι]
    (s : Finset I) (a : Stage I r s) (b : ι → Stage I r s)
    (h : PrimeSpectrum.basicOpen (toQuotient R I r s a) ≤
      ⨆ i, PrimeSpectrum.basicOpen (toQuotient R I r s (b i))) :
    ∃ (t : Finset I) (hst : s ≤ t), ∀ (q : Finset I) (htq : t ≤ q),
      PrimeSpectrum.basicOpen (transition R I r (hst.trans htq) a) ≤
        ⨆ i, PrimeSpectrum.basicOpen (transition R I r (hst.trans htq) (b i)) := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp ((basicOpen_le_iSup_iff _ _).mp h)
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hn
  choose c₀ hc₀ using fun i ↦ toQuotient_surjective R I r s (c i)
  have he : toQuotient R I r s (∑ i, c₀ i * b i) = toQuotient R I r s (a ^ n) := by
    simpa only [map_sum, map_mul, hc₀, map_pow] using hc
  obtain ⟨t, hst, ht⟩ := exists_transition_eq R I r s _ _ he
  refine ⟨t, hst, fun q htq ↦ (basicOpen_le_iSup_iff _ _).mpr ?_⟩
  apply Ideal.mem_radical_iff.mpr
  refine ⟨n, Ideal.mem_span_range_iff_exists_fun.mpr
    ⟨fun i ↦ transition R I r (hst.trans htq) (c₀ i), ?_⟩⟩
  have hq := congrArg (transition R I r htq) ht
  simpa only [← AlgHom.comp_apply, transition_comp, map_sum, map_mul, map_pow] using hq

/-- Finitely many finite-union inclusions descend simultaneously. -/
theorem exists_localized_principal_union_inclusions_tail
    {ν : Type*} [Finite ν] {μ : ν → Type*} [∀ n, Finite (μ n)]
    (s : Finset I) (a : ν → Stage I r s) (b : ∀ n, μ n → Stage I r s)
    (h : ∀ n, PrimeSpectrum.basicOpen (toQuotient R I r s (a n)) ≤
      ⨆ m, PrimeSpectrum.basicOpen (toQuotient R I r s (b n m))) :
    ∃ (t : Finset I) (hst : s ≤ t), ∀ (q : Finset I) (htq : t ≤ q) (n : ν),
      PrimeSpectrum.basicOpen (transition R I r (hst.trans htq) (a n)) ≤
        ⨆ m, PrimeSpectrum.basicOpen (transition R I r (hst.trans htq) (b n m)) := by
  classical
  let _ := Fintype.ofFinite ν
  choose t hst ht using fun n ↦
    exists_localized_principal_union_inclusion_tail I r s (a n) (b n) (h n)
  refine ⟨s ∪ Finset.univ.biUnion t, Finset.subset_union_left, fun q hq n ↦ ?_⟩
  have hn : t n ≤ q := by
    apply le_trans ?_ hq
    intro z hz
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨n, Finset.mem_univ _, hz⟩)
  exact ht n q hn

end FLT.Mazur.FiniteRelationLocalization
