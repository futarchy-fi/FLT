/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Finiteness.Basic

/-! # Spread equality of finitely generated ideals from a prime -/

@[expose] public noncomputable section

namespace Ideal

variable {R : Type*} [CommRing R]

/-- Finitely many localized ideal-membership witnesses have one common denominator. -/
theorem exists_away_map_le_of_atPrime (p : Ideal R) [p.IsPrime]
    (I J : Ideal R) (hI : I.FG)
    (h : I.map (algebraMap R (Localization.AtPrime p)) ≤
      J.map (algebraMap R (Localization.AtPrime p))) :
    ∃ a ∉ p, I.map (algebraMap R (Localization.Away a)) ≤
      J.map (algebraMap R (Localization.Away a)) := by
  classical
  obtain ⟨t, ht⟩ := hI
  have hex (x : t) : ∃ s : p.primeCompl, (s : R) * (x : R) ∈ J := by
    have hx : (x : R) ∈ I := ht ▸ subset_span x.property
    obtain ⟨s, hs, hx⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl
        (Localization.AtPrime p) J x).mp (h (mem_map_of_mem _ hx))
    exact ⟨⟨s, hs⟩, hx⟩
  choose s hs using hex
  let d : p.primeCompl := ∏ x : t, s x
  refine ⟨d.val, d.property, ?_⟩
  rw [map_le_iff_le_comap, ← ht, span_le]
  intro x hx
  change algebraMap R (Localization.Away d.val) x ∈
    J.map (algebraMap R (Localization.Away d.val))
  apply (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (Submonoid.powers d.val) (Localization.Away d.val) J x).mpr
  refine ⟨d.val, Submonoid.mem_powers _, ?_⟩
  have hd : (s ⟨x, hx⟩ : R) ∣ d.val := by
    simpa [d] using Finset.dvd_prod_of_mem (fun y : t ↦ (s y : R)) (Finset.mem_univ ⟨x, hx⟩)
  obtain ⟨c, hc⟩ := hd
  have hmem := J.mul_mem_left c (hs ⟨x, hx⟩)
  convert hmem using 1; rw [hc]; ring

/-- A subideal that generates a finite ideal at a prime generates it on a principal
neighbourhood. This controls the entire kernel, not only the displayed relations. -/
theorem exists_away_map_eq_of_atPrime (p : Ideal R) [p.IsPrime]
    (I J : Ideal R) (hI : I.FG) (hJI : J ≤ I)
    (h : I.map (algebraMap R (Localization.AtPrime p)) =
      J.map (algebraMap R (Localization.AtPrime p))) :
    ∃ a ∉ p, I.map (algebraMap R (Localization.Away a)) =
      J.map (algebraMap R (Localization.Away a)) := by
  obtain ⟨a, ha, hle⟩ := exists_away_map_le_of_atPrime p I J hI h.le
  exact ⟨a, ha, le_antisymm hle (map_mono hJI)⟩

/-- Equality of localized ideals persists when the denominator is replaced by a multiple. -/
theorem map_eq_away_of_dvd (I J : Ideal R) {a b : R} (hab : a ∣ b)
    (h : I.map (algebraMap R (Localization.Away a)) =
      J.map (algebraMap R (Localization.Away a))) :
    I.map (algebraMap R (Localization.Away b)) =
      J.map (algebraMap R (Localization.Away b)) := by
  let f : Localization.Away a →+* Localization.Away b :=
    IsLocalization.Away.lift a (IsLocalization.Away.isUnit_of_dvd b hab)
  have hf : f.comp (algebraMap R (Localization.Away a)) =
      algebraMap R (Localization.Away b) := by
    ext x
    exact IsLocalization.Away.lift_eq a (IsLocalization.Away.isUnit_of_dvd b hab) x
  simpa only [Ideal.map_map, hf] using congrArg (Ideal.map f) h

end Ideal
