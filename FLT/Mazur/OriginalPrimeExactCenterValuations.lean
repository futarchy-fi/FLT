/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalPrimeDomainValuationObstruction
public import FLT.Mazur.ValuationExactCenterIntegralTests

/-!
# Original-prime poles with the exact original center

Residue refinement repairs the possible strict generization in an arbitrary
valuation witness. All scalar coordinates and the same pole are retained.
The domain case uses the canonical fraction field of the original localization.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.OriginalPrimeIntegralFiber
open IsLocalRing ValuationSubringIntegralTests
variable {R B K : Type*} [CommRing R] [CommRing B] [Field K]
  (s : R →+* B) (P : Ideal R) [P.IsPrime]
local notation "T" => Localization (P.primeCompl.map s)
local notation "L" => Localization.AtPrime P
local notation "τ" => localizedMap s P
variable (φ : Localization (P.primeCompl.map s) →+* K) (hφ : Function.Injective φ)

include hφ in
/-- A nonintegral coordinate has a pole centered at precisely the chosen original prime. -/
theorem exists_exact_center_pole (b : B)
    (h : ¬ (τ).IsIntegralElem (algebraMap B T b)) :
    ∃ (V : ValuationSubring K) (f : R →+* V),
      V.subtype.comp f = φ.comp ((algebraMap B T).comp s) ∧
        (maximalIdeal V).comap f = P ∧ φ (algebraMap B T b) ∉ V := by
  have hn : ¬ (φ.comp τ).IsIntegralElem (φ (algebraMap B T b)) :=
    fun hi ↦ h (RingHom.IsIntegralElem.of_map hφ hi)
  obtain ⟨V, f, hf, hc, hx⟩ :=
    exists_exact_center_valuation_of_not_integral (φ.comp τ) _ hn
  refine ⟨V, f.comp (algebraMap R L), ?_, ?_, hx⟩
  · rw [← RingHom.comp_assoc, hf, RingHom.comp_assoc, localizedMap_comp]
  · rw [← Ideal.comap_comap, hc]
    exact Localization.AtPrime.under_maximalIdeal

include hφ in
/-- Exact original centers already detect an original avoiding polynomial equation. -/
theorem equation_of_exact_center_regular (b : B)
    (h : ∀ (V : ValuationSubring K) (f : R →+* V),
      V.subtype.comp f = φ.comp ((algebraMap B T).comp s) →
        (maximalIdeal V).comap f = P → φ (algebraMap B T b) ∈ V) :
    ∃ p : Polynomial R, p.eval₂ s b = 0 ∧ p.leadingCoeff ∉ P := by
  apply exists_equation_of_localized_integral
  by_contra hn
  obtain ⟨V, f, hf, hc, hx⟩ := exists_exact_center_pole s P φ hφ b hn
  exact hx (h V f hf hc)

include hφ in
/-- Fixed generator regularity at the exact prime proves full original local integrality. -/
theorem localizedMap_integral_of_exact_center_regular (S : Set B)
    (hgen : Subring.closure (Set.range s ∪ S) = ⊤)
    (h : ∀ (V : ValuationSubring K) (f : R →+* V),
      V.subtype.comp f = φ.comp ((algebraMap B T).comp s) →
        (maximalIdeal V).comap f = P → ∀ b ∈ S, φ (algebraMap B T b) ∈ V) :
    (τ).IsIntegral := by
  apply localizedMap_integral_of_generator_equations s P S hgen
  exact fun b hb ↦ equation_of_exact_center_regular s P φ hφ b
    (fun V f hf hc ↦ h V f hf hc b hb)

variable [IsDomain B]

/-- A failed domain equation constructs an exact-center pole without an assumed field embedding. -/
theorem exists_fraction_exact_center_pole (b : B)
    (h : ∀ p : Polynomial R, p.eval₂ s b = 0 → p.leadingCoeff ∈ P) :
    let hn : ¬ (τ).IsIntegral := fun hi ↦ by
      obtain ⟨p, hp, hl⟩ := exists_equation_of_localized_integral s P b (hi _)
      exact hl (h p hp)
    let _ := localization_domain_of_not_integral s P hn
    ∃ (V : ValuationSubring (FractionRing T)) (f : R →+* V),
      V.subtype.comp f =
        (algebraMap T (FractionRing T)).comp ((algebraMap B T).comp s) ∧
      (maximalIdeal V).comap f = P ∧
        algebraMap T (FractionRing T) (algebraMap B T b) ∉ V := by
  let hn : ¬ (τ).IsIntegral := fun hi ↦ by
    obtain ⟨p, hp, hl⟩ := exists_equation_of_localized_integral s P b (hi _)
    exact hl (h p hp)
  let _ := localization_domain_of_not_integral s P hn
  apply exists_exact_center_pole s P (algebraMap T (FractionRing T))
    (IsFractionRing.injective T (FractionRing T)) b
  intro hi
  obtain ⟨p, hp, hl⟩ := exists_equation_of_localized_integral s P b hi
  exact hl (h p hp)

end FLT.Mazur.OriginalPrimeIntegralFiber
