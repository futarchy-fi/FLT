/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Attained ceilings for components over an original scalar prime

A bounded family of ranked components has a least bound over all scalar
centers contained in a fixed prime. A strict excess over the baseline is
attained by a component, including when the fiber at the prime is empty.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarComponentRank
variable {T ι : Type*} [CommRing T]
  (center : ι → PrimeSpectrum T) (rank : ι → ℕ) (base : ℕ)
  (bounded : ∃ N : ℕ, ∀ i, rank i ≤ N)

include bounded in
/-- Bounded component ranks have a bound that also includes the baseline. -/
theorem exists_bound (P : PrimeSpectrum T) :
    ∃ N : ℕ, base ≤ N ∧ ∀ i, (center i).asIdeal ≤ P.asIdeal → rank i ≤ N := by
  obtain ⟨N, hN⟩ := bounded
  exact ⟨max base N, le_max_left _ _, fun i _ ↦ (hN i).trans (le_max_right _ _)⟩

/-- The least rank bound, with the baseline retained even if no component lies over the center. -/
def ceiling (P : PrimeSpectrum T) : ℕ := by
  classical
  exact Nat.find (exists_bound center rank base bounded P)

/-- The baseline is bounded without assuming any scalar fiber is nonempty. -/
theorem base_le (P : PrimeSpectrum T) : base ≤ ceiling center rank base bounded P := by
  classical
  exact (Nat.find_spec (exists_bound center rank base bounded P)).1

/-- Every component whose scalar center generizes the original prime satisfies the ceiling. -/
theorem rank_le (P : PrimeSpectrum T) (i : ι) (hi : (center i).asIdeal ≤ P.asIdeal) :
    rank i ≤ ceiling center rank base bounded P := by
  classical
  exact (Nat.find_spec (exists_bound center rank base bounded P)).2 i hi

/-- Any bound on the baseline and all relevant components bounds the constructed ceiling. -/
theorem minimal (P : PrimeSpectrum T) (N : ℕ) (hb : base ≤ N)
    (hN : ∀ i, (center i).asIdeal ≤ P.asIdeal → rank i ≤ N) :
    ceiling center rank base bounded P ≤ N := by
  classical
  exact Nat.find_min' _ ⟨hb, hN⟩

/-- A ceiling bound tests every generizing center, rather than only the exact scalar fiber. -/
theorem le_iff (P : PrimeSpectrum T) (N : ℕ) :
    ceiling center rank base bounded P ≤ N ↔
      base ≤ N ∧ ∀ i, (center i).asIdeal ≤ P.asIdeal → rank i ≤ N := by
  constructor
  · intro h
    exact ⟨(base_le center rank base bounded P).trans h,
      fun i hi ↦ (rank_le center rank base bounded P i hi).trans h⟩
  · exact fun h ↦ minimal center rank base bounded P N h.1 h.2

/-- The least bound increases under specialization of the unchanged scalar prime. -/
theorem monotone : Monotone (ceiling center rank base bounded) := by
  intro P Q hPQ
  apply minimal center rank base bounded P _ (base_le center rank base bounded Q)
  intro i hi
  exact rank_le center rank base bounded Q i (hi.trans hPQ)

/-- Any strict excess is attained by an actual component with a generizing original center. -/
theorem attained_of_lt (P : PrimeSpectrum T)
    (h : base < ceiling center rank base bounded P) :
    ∃ i, (center i).asIdeal ≤ P.asIdeal ∧ rank i = ceiling center rank base bounded P := by
  classical
  by_contra hn
  have hm : ceiling center rank base bounded P ≤ ceiling center rank base bounded P - 1 := by
    apply minimal center rank base bounded P _ (by omega)
    intro i hi
    have hl := rank_le center rank base bounded P i hi
    have he : rank i ≠ ceiling center rank base bounded P := fun he ↦ hn ⟨i, hi, he⟩
    omega
  omega

/-- The chosen maximal component has the same ceiling at its own actual scalar center. -/
theorem attained_at_own_center (P : PrimeSpectrum T)
    (h : base < ceiling center rank base bounded P) :
    ∃ i, (center i).asIdeal ≤ P.asIdeal ∧
      rank i = ceiling center rank base bounded P ∧
      ceiling center rank base bounded (center i) = ceiling center rank base bounded P := by
  obtain ⟨i, hi, hr⟩ := attained_of_lt center rank base bounded P h
  refine ⟨i, hi, hr, Nat.le_antisymm (monotone center rank base bounded hi) ?_⟩
  rw [← hr]
  exact rank_le center rank base bounded (center i) i le_rfl

/-- Each failed proposed rank bound has an actual higher component, with the maximal rank. -/
theorem exists_higher_iff (P : PrimeSpectrum T) (N : ℕ) (hb : base ≤ N) :
    N < ceiling center rank base bounded P ↔
      ∃ i, (center i).asIdeal ≤ P.asIdeal ∧ N < rank i := by
  constructor
  · intro h
    obtain ⟨i, hi, hr⟩ := attained_of_lt center rank base bounded P (hb.trans_lt h)
    exact ⟨i, hi, hr ▸ h⟩
  · rintro ⟨i, hi, hr⟩
    exact hr.trans_le (rank_le center rank base bounded P i hi)

end FLT.Mazur.ScalarComponentRank
