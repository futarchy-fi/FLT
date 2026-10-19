/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarTestLocalizationKernels
public import FLT.Mazur.OriginalPrimeIntegralGenerators

/-!
# Full test equations from integral principal charts and exact fibers

Integrality is required on the principal chart where a test is invertible,
localized at the unchanged scalar prime. Integrality of the whole coefficient
algebra alone would not suffice. An empty exact test fiber then constructs
an original power equation, retaining all nilpotents.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarTestLocalization
open OriginalPrimeIntegralFiber ScalarLocalizedIdealNilpotence
variable {R B : Type*} [CommRing R] [CommRing B]
  (s : R →+* B) (P : PrimeSpectrum R) (b : B)
set_option quotPrecheck false
local notation "τ" => (algebraMap B (Localization.Away b)).comp s

/-- Exact vanishing of a test makes its entire principal chart fiber empty. -/
theorem testChart_empty_fiber
    (hf : ∀ Q : PrimeSpectrum B, PrimeSpectrum.comap s Q = P → b ∈ Q.asIdeal) :
    ∀ Q : PrimeSpectrum (Localization.Away b), Q.asIdeal.comap τ ≠ P.asIdeal := by
  intro Q hQ
  let q := PrimeSpectrum.comap (algebraMap B (Localization.Away b)) Q
  have hp : PrimeSpectrum.comap s q = P := PrimeSpectrum.ext hQ
  exact Q.asIdeal.notMem_of_isUnit (IsLocalization.Away.algebraMap_isUnit b)
    (hf q hp)

/-- Local integrality upgrades exact-fiber vanishing to a full original power equation. -/
theorem equation_of_integral_testChart
    (hi : (localizedMap τ P.asIdeal).IsIntegral)
    (hf : ∀ Q : PrimeSpectrum B, PrimeSpectrum.comap s Q = P → b ∈ Q.asIdeal) :
    ∃ (r : R) (k : ℕ), r ∉ P.asIdeal ∧ b ^ k * s r = 0 := by
  obtain ⟨r, hr, he⟩ := exists_kernel_scalar τ P.asIdeal hi (testChart_empty_fiber s P b hf)
  obtain ⟨k, hk⟩ := (mem_testKernel s b r).mp he
  exact ⟨r, k, hr, hk⟩

/-- Finite generator equations on the principal chart supply the local integrality input. -/
theorem equation_of_testChart_generators (G : Set (Localization.Away b))
    (hG : Subring.closure (Set.range τ ∪ G) = ⊤)
    (hg : ∀ x ∈ G, ∃ p : Polynomial R, p.eval₂ τ x = 0 ∧ p.leadingCoeff ∉ P.asIdeal)
    (hf : ∀ Q : PrimeSpectrum B, PrimeSpectrum.comap s Q = P → b ∈ Q.asIdeal) :
    ∃ (r : R) (k : ℕ), r ∉ P.asIdeal ∧ b ^ k * s r = 0 :=
  equation_of_integral_testChart s P b
    (localizedMap_integral_of_generator_equations τ P.asIdeal G hG hg) hf

/-- Exact tests and integral principal charts construct a denominator for a whole ideal power. -/
theorem power_denominator_of_integral_testCharts (a : Finset B)
    (hi : ∀ b ∈ a, (localizedMap
      ((algebraMap B (Localization.Away b)).comp s) P.asIdeal).IsIntegral)
    (hf : ∀ Q : PrimeSpectrum B, PrimeSpectrum.comap s Q = P →
      ∀ b ∈ a, b ∈ Q.asIdeal) :
    ∃ (k : ℕ) (r : R), r ∉ P.asIdeal ∧
      s r ∈ ((Ideal.span (a : Set B)) ^ k).annihilator := by
  apply power_annihilator_of_kernels s a P
  intro b hb
  obtain ⟨r, k, hr, he⟩ := equation_of_integral_testChart s P b (hi b hb)
    (fun Q hQ ↦ hf Q hQ b hb)
  exact ⟨r, hr, (mem_testKernel s b r).mpr ⟨k, he⟩⟩

end FLT.Mazur.ScalarTestLocalization
