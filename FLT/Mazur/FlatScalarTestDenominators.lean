/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarNilpotenceFlatBaseChange
public import FLT.Mazur.FlatScalarPowerKernel

/-!
# Constructing original denominators from arbitrary flat branch equations

Each test may have its own branch function. Exact flat kernel transport
extracts original scalar equations, then the finite kernel product constructs
one original scalar annihilating a whole power of the original test ideal.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.ScalarTestLocalization
open ScalarLocalizedIdealNilpotence
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
  (S : Type*) [CommRing S] [Algebra R S] [Module.Flat R S]
local notation "B'" => S ⊗[R] B
local notation "j" => Algebra.TensorProduct.includeRight (R := R) (A := S) (B := B)

/-- Independently chosen branch functions yield a whole original ideal-power denominator. -/
theorem original_power_denominator_of_flat (a : Finset B) (Q : PrimeSpectrum S)
    (h : ∀ b ∈ a, ∃ (x : S) (k : ℕ), x ∉ Q.asIdeal ∧
      (j b) ^ k * algebraMap S B' x = 0) :
    ∃ (k : ℕ) (r : R), r ∉ Q.asIdeal.comap (algebraMap R S) ∧
      algebraMap R B r ∈ ((Ideal.span (a : Set B)) ^ k).annihilator := by
  apply power_annihilator_of_kernels (algebraMap R B) a
    (PrimeSpectrum.comap (algebraMap R S) Q)
  intro b hb
  obtain ⟨x, k, hx, he⟩ := h b hb
  obtain ⟨r, hr, hm⟩ :=
    FlatScalarPowerKernel.original_equation_same_power S Q b k x hx he
  exact ⟨r, hr, (mem_testKernel _ _ _).mpr ⟨k, hm⟩⟩

/-- The constructed original scalar cuts out a full neighborhood with actual ideal nilpotence. -/
theorem original_power_neighborhood_of_flat (a : Finset B) (Q : PrimeSpectrum S)
    (h : ∀ b ∈ a, ∃ (x : S) (k : ℕ), x ∉ Q.asIdeal ∧
      (j b) ^ k * algebraMap S B' x = 0) :
    ∃ (k : ℕ) (r : R), r ∉ Q.asIdeal.comap (algebraMap R S) ∧
      ((Ideal.span (a : Set B)).map
        (algebraMap B (Localization.Away (algebraMap R B r)))) ^ k = ⊥ := by
  obtain ⟨k, r, hr, he⟩ := original_power_denominator_of_flat S a Q h
  exact ⟨k, r, hr, FiniteIdealLocalizationDenominators.away_power_eq_bot _ k _ he⟩

end FLT.Mazur.ScalarTestLocalization
