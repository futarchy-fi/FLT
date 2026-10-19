/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MinimalPrimeLocalizedIdeal
public import Mathlib.RingTheory.Ideal.Colon

/-!
# Denominators for finite ideal power equations

A zero localized finite ideal has one denominator annihilating the entire
original ideal. Applied to powers, this spreads generic local nilpotence to
an actual principal neighborhood without reducing the coefficient ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteIdealLocalizationDenominators
variable {R : Type*} [CommRing R]

private theorem finite_common_annihilator (S : Submonoid R) (a : Finset R)
    (h : ∀ x ∈ a, ∃ u : S, (u : R) * x = 0) :
    ∃ u : S, ∀ x ∈ a, (u : R) * x = 0 := by
  classical
  induction a using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | @insert x a hx ih =>
    obtain ⟨u, hu⟩ := h x (Finset.mem_insert_self _ _)
    obtain ⟨v, hv⟩ := ih (fun y hy ↦ h y (Finset.mem_insert_of_mem hy))
    refine ⟨u * v, fun y hy ↦ ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · change (u : R) * v * y = 0
      rw [mul_right_comm, hu, zero_mul]
    · change (u : R) * v * y = 0
      rw [mul_assoc, hv y hy, mul_zero]

/-- One denominator kills the entire original finite ideal whose localization is zero. -/
theorem exists_annihilator (I : Ideal R) (hI : I.FG) (S : Submonoid R)
    (h : I.map (algebraMap R (Localization S)) = ⊥) :
    ∃ u : S, (u : R) ∈ I.annihilator := by
  classical
  obtain ⟨a, ha⟩ := hI
  have he (x : R) (hx : x ∈ a) : ∃ u : S, (u : R) * x = 0 := by
    apply (IsLocalization.map_eq_zero_iff S (Localization S) x).mp
    have hm := Ideal.mem_map_of_mem (algebraMap R (Localization S))
      (ha ▸ (Ideal.subset_span hx) : x ∈ I)
    rwa [h, Ideal.mem_bot] at hm
  obtain ⟨u, hu⟩ := finite_common_annihilator S a he
  refine ⟨u, ?_⟩
  rw [← ha, Submodule.mem_annihilator_span]
  exact fun x ↦ hu x.val x.property

/-- The same original denominator kills a power before any coefficients are localized. -/
theorem exists_power_annihilator (I : Ideal R) (hI : I.FG) (S : Submonoid R)
    (h : IsNilpotent (I.map (algebraMap R (Localization S)))) :
    ∃ k : ℕ, ∃ u : S, (u : R) ∈ (I ^ k).annihilator := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, exists_annihilator (I ^ k) hI.pow S ?_⟩
  rwa [Ideal.map_pow]

/-- Inverting any annihilating denominator makes the original ideal power exactly zero. -/
theorem away_power_eq_bot (I : Ideal R) (k : ℕ) (u : R)
    (hu : u ∈ (I ^ k).annihilator) :
    (I.map (algebraMap R (Localization.Away u))) ^ k = ⊥ := by
  rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]
  intro x hx
  apply (IsLocalization.map_eq_zero_iff (Submonoid.powers u) (Localization.Away u) x).mpr
  exact ⟨⟨u, Submonoid.mem_powers u⟩, Submodule.mem_annihilator.mp hu x hx⟩

/-- At a minimal prime containing the tests, a principal neighborhood has one actual power order. -/
theorem exists_minimal_neighborhood (I : Ideal R) (hI : I.FG) (Q : minimalPrimes R)
    (hQ : I ≤ Q.val) :
    ∃ k : ℕ, ∃ u : R, u ∉ Q.val ∧ u ∈ (I ^ k).annihilator ∧
      (I.map (algebraMap R (Localization.Away u))) ^ k = ⊥ := by
  let _ := Q.property.1.1
  obtain ⟨k, u, hu⟩ := exists_power_annihilator I hI Q.val.primeCompl
    ((MinimalPrimeLocalizedIdeal.localized_nilpotent_iff I hI Q).mpr hQ)
  exact ⟨k, u, u.property, hu, away_power_eq_bot I k u hu⟩

end FLT.Mazur.FiniteIdealLocalizationDenominators
