/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Localization.PrincipalIdealComparison
public import FLT.Mathlib.RingTheory.Regular.ClearLocalizedRelations
public import FLT.Mathlib.RingTheory.Regular.PrincipalRefinement

/-! # Regular local ideal presentations spread with their full relation ideal -/

@[expose] public noncomputable section

namespace RingTheory.Sequence

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

/-- Clear a regular local presentation and spread both regularity and the kernel to
one principal neighbourhood. The displayed list has the original number of relations. -/
theorem exists_away_regular_ideal_presentation (p I : Ideal R) [p.IsPrime]
    (rs : List (Localization.AtPrime p)) (hreg : IsRegular (Localization.AtPrime p) rs)
    (hI : Ideal.ofList rs = I.map (algebraMap R (Localization.AtPrime p))) :
    ∃ (a : R) (qs : List R), a ∉ p ∧ (∀ q ∈ qs, q ∈ I) ∧ qs.length = rs.length ∧
      IsRegular (Localization.Away a) (qs.map (algebraMap R (Localization.Away a))) ∧
      Ideal.ofList (qs.map (algebraMap R (Localization.Away a))) =
        I.map (algebraMap R (Localization.Away a)) := by
  have hmem : ∀ x ∈ rs, x ∈ I.map (algebraMap R (Localization.AtPrime p)) := by
    intro x hx
    rw [← hI]
    exact Ideal.subset_span hx
  obtain ⟨qs, hqs, hlen, hspan, hreg'⟩ :=
    exists_numerators_of_localized_regular_list p.primeCompl I rs hmem hreg
  have hJI : Ideal.ofList qs ≤ I := Ideal.span_le.mpr hqs
  have hloc : I.map (algebraMap R (Localization.AtPrime p)) =
      (Ideal.ofList qs).map (algebraMap R (Localization.AtPrime p)) := by
    rw [Ideal.map_ofList, hspan, hI]
  obtain ⟨a, ha, hgen⟩ := Ideal.exists_away_map_eq_of_atPrime p I (Ideal.ofList qs)
    (IsNoetherian.noetherian I) hJI hloc
  obtain ⟨b, hb, hregb⟩ := exists_isRegular_away_of_atPrime p qs hreg'
  have hab : a * b ∉ p := p.primeCompl.mul_mem ha hb
  refine ⟨a * b, qs, hab, hqs, hlen, ?_, ?_⟩
  · exact isRegular_ring_away_of_dvd_of_atPrime p (dvd_mul_left b a) hab qs hregb hreg'
  · rw [← Ideal.map_ofList]
    exact (Ideal.map_eq_away_of_dvd I (Ideal.ofList qs) (dvd_mul_right a b) hgen).symm

/-- The chart quotient isomorphism fixes original ring coordinates. -/
theorem exists_away_regular_quotient_presentation (p I : Ideal R) [p.IsPrime]
    (rs : List (Localization.AtPrime p)) (hreg : IsRegular (Localization.AtPrime p) rs)
    (hI : Ideal.ofList rs = I.map (algebraMap R (Localization.AtPrime p))) :
    ∃ (a : R) (qs : List R), a ∉ p ∧ qs.length = rs.length ∧
      IsRegular (Localization.Away a) (qs.map (algebraMap R (Localization.Away a))) ∧
      ∃ e : (Localization.Away a ⧸
          Ideal.ofList (qs.map (algebraMap R (Localization.Away a)))) ≃ₐ[R]
          (Localization.Away a ⧸ I.map (algebraMap R (Localization.Away a))),
        ∀ r : R, e (algebraMap R _ r) = algebraMap R _ r := by
  obtain ⟨a, qs, ha, _, hlen, hreg, hgen⟩ :=
    exists_away_regular_ideal_presentation p I rs hreg hI
  exact ⟨a, qs, ha, hlen, hreg, Ideal.quotientEquivAlgOfEq R hgen, fun _ ↦ rfl⟩

end RingTheory.Sequence
