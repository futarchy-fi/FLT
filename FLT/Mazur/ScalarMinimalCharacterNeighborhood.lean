/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarMinimalCharacterPropagation
public import FLT.Mazur.ScalarTestLocalizationKernels

/-!
# Construct original scalar neighborhoods from generic characters

Going down and vanishing on minimal scalar fibers produce one original scalar
outside the prescribed prime annihilating an entire power of a finite ideal.
This retains the coefficient ring and all its nilpotents. For a finite family
of tests the same scalar lies in every full principal test-chart kernel.
-/

@[expose] public noncomputable section
universe u
namespace FLT.Mazur.ScalarTestLocalization
open ScalarLocalizedIdealNilpotence
variable {R B : Type u} [CommRing R] [CommRing B]
  (s : R →+* B) (P : PrimeSpectrum R)

/-- Generic character vanishing constructs one scalar and an actual whole-ideal equation. -/
theorem scalar_neighborhood_of_minimal_characters (J : Ideal B) (hJfg : J.FG)
    (hs : s.FiniteType) (hg : GeneralizingMap (PrimeSpectrum.comap s))
    (hJ : ∀ Q : PrimeSpectrum R, Q.asIdeal ∈ minimalPrimes R → Q ≤ P →
      ∀ χ : B →+* AlgebraicClosure Q.asIdeal.ResidueField,
        χ.comp s = algebraMap R _ → J ≤ RingHom.ker χ) :
    ∃ (k : ℕ) (r : R), r ∉ P.asIdeal ∧ s r ∈ (J ^ k).annihilator ∧
      (J.map (algebraMap B (Localization.Away (s r)))) ^ k = ⊥ := by
  apply exists_scalar_neighborhood s J P.asIdeal hJfg
  intro q hq
  exact ideal_le_prime_of_minimal_scalar_characters s P J hs hg hJ
    ⟨q.val, q.property.1.1⟩ hq

/-- One scalar works on every full principal test chart and kills their common ideal power. -/
theorem scalar_test_kernels_of_minimal_characters (a : Finset B)
    (hs : s.FiniteType) (hg : GeneralizingMap (PrimeSpectrum.comap s))
    (ha : ∀ Q : PrimeSpectrum R, Q.asIdeal ∈ minimalPrimes R → Q ≤ P →
      ∀ χ : B →+* AlgebraicClosure Q.asIdeal.ResidueField,
        χ.comp s = algebraMap R _ → ∀ t ∈ a, χ t = 0) :
    ∃ (k : ℕ) (r : R), r ∉ P.asIdeal ∧
      s r ∈ ((Ideal.span (a : Set B)) ^ k).annihilator ∧
      (∀ t ∈ a, r ∈ testKernel s t) ∧
      ((Ideal.span (a : Set B)).map
        (algebraMap B (Localization.Away (s r)))) ^ k = ⊥ := by
  have hJ : ∀ Q : PrimeSpectrum R, Q.asIdeal ∈ minimalPrimes R → Q ≤ P →
      ∀ χ : B →+* AlgebraicClosure Q.asIdeal.ResidueField,
        χ.comp s = algebraMap R _ → Ideal.span (a : Set B) ≤ RingHom.ker χ := by
    intro Q hQ hQP χ hχ
    exact Ideal.span_le.mpr (fun t ht ↦ ha Q hQ hQP χ hχ t ht)
  obtain ⟨k, r, hr, he, hz⟩ := scalar_neighborhood_of_minimal_characters s P
    (Ideal.span (a : Set B)) (Submodule.fg_span a.finite_toSet) hs hg hJ
  exact ⟨k, r, hr, he, scalar_annihilator_mem_kernels s a k r he, hz⟩

end FLT.Mazur.ScalarTestLocalization
