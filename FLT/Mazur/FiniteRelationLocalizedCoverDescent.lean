/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationLocalizationDetection
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Finite covers inside localized relation models

A finite cover in an original localized overlap descends to every stage of
one tail. The proof transports a finite unit-ideal certificate and therefore
persists under any subsequent occurrence refinement.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationLocalization

universe u v w

variable {R : Type u} [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P) (r : P)

/-- A finite principal cover of a localized quotient holds on a whole relation tail. -/
theorem exists_localized_principal_cover_tail {ι : Type w} [Finite ι] (s : Finset I)
    (d : ι → Stage I r s)
    (hd : (⨆ i, PrimeSpectrum.basicOpen (toQuotient R I r s (d i))) = ⊤) :
    ∃ (t : Finset I) (hst : s ≤ t), ∀ (q : Finset I) (htq : t ≤ q),
      (⨆ i, PrimeSpectrum.basicOpen (transition R I r (hst.trans htq) (d i))) = ⊤ := by
  classical
  let _ := Fintype.ofFinite ι
  have hspan := PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp hd
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp
    (show (1 : Quotient I r) ∈ Ideal.span (Set.range fun i ↦ toQuotient R I r s (d i)) by
      rw [hspan]
      trivial)
  choose a ha using fun i ↦ toQuotient_surjective R I r s (c i)
  have he : toQuotient R I r s (∑ i, a i * d i) = toQuotient R I r s 1 := by
    simpa only [map_sum, map_mul, ha, map_one] using hc
  obtain ⟨t, hst, ht⟩ := exists_transition_eq R I r s (∑ i, a i * d i) 1 he
  refine ⟨t, hst, fun q htq ↦ ?_⟩
  have hsum : ∑ i, transition R I r (hst.trans htq) (a i) *
      transition R I r (hst.trans htq) (d i) = 1 := by
    have h := congrArg (transition R I r htq) ht
    simpa only [map_sum, map_mul, map_one, ← AlgHom.comp_apply, transition_comp] using h
  apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr
  apply Ideal.eq_top_of_isUnit_mem _ ?_ isUnit_one
  exact Ideal.mem_span_range_iff_exists_fun.mpr ⟨_, hsum⟩

end FLT.Mazur.FiniteRelationLocalization
