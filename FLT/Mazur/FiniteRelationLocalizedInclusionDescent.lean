/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationLocalizationDetection
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Principal image inclusions descend on a relation tail

A basic-open inclusion in the original localized quotient has a finite
power-divisibility certificate. Lifting its coefficient and imposing its
single equation makes the inclusion persist on every later relation stage.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationLocalization

universe u v

variable {R : Type u} [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P) (r : P)

/-- A principal inclusion of the localized quotient holds on an entire relation tail. -/
theorem exists_localized_principal_inclusion_tail (s : Finset I) (a b : Stage I r s)
    (h : PrimeSpectrum.basicOpen (toQuotient R I r s a) ≤
      PrimeSpectrum.basicOpen (toQuotient R I r s b)) :
    ∃ (t : Finset I) (hst : s ≤ t), ∀ (q : Finset I) (htq : t ≤ q),
      PrimeSpectrum.basicOpen (transition R I r (hst.trans htq) a) ≤
        PrimeSpectrum.basicOpen (transition R I r (hst.trans htq) b) := by
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp
    ((PrimeSpectrum.basicOpen_le_basicOpen_iff _ _).mp h)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hn
  obtain ⟨c₀, hc₀⟩ := toQuotient_surjective R I r s c
  have he : toQuotient R I r s (a ^ n) = toQuotient R I r s (b * c₀) := by
    simpa only [map_pow, map_mul, hc₀] using hc
  obtain ⟨t, hst, ht⟩ := exists_transition_eq R I r s (a ^ n) (b * c₀) he
  refine ⟨t, hst, fun q htq ↦ ?_⟩
  apply (PrimeSpectrum.basicOpen_le_basicOpen_iff _ _).mpr
  apply Ideal.mem_radical_iff.mpr
  refine ⟨n, Ideal.mem_span_singleton.mpr ⟨transition R I r (hst.trans htq) c₀, ?_⟩⟩
  have hq := congrArg (transition R I r htq) ht
  simpa only [← AlgHom.comp_apply, transition_comp, map_pow, map_mul] using hq

/-- A finite family of principal image inclusions holds simultaneously on one tail. -/
theorem exists_localized_principal_inclusions_tail {ι : Type*} [Finite ι]
    (s : Finset I) (a b : ι → Stage I r s)
    (h : ∀ i, PrimeSpectrum.basicOpen (toQuotient R I r s (a i)) ≤
      PrimeSpectrum.basicOpen (toQuotient R I r s (b i))) :
    ∃ (t : Finset I) (hst : s ≤ t), ∀ (q : Finset I) (htq : t ≤ q) (i : ι),
      PrimeSpectrum.basicOpen (transition R I r (hst.trans htq) (a i)) ≤
        PrimeSpectrum.basicOpen (transition R I r (hst.trans htq) (b i)) := by
  classical
  let _ := Fintype.ofFinite ι
  choose t hst ht using fun i ↦ exists_localized_principal_inclusion_tail I r s (a i) (b i) (h i)
  refine ⟨s ∪ Finset.univ.biUnion t, Finset.subset_union_left, fun q hq i ↦ ?_⟩
  have hi : t i ≤ q := by
    apply le_trans ?_ hq
    intro z hz
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hz⟩)
  exact ht i q hi

end FLT.Mazur.FiniteRelationLocalization
