/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalPrimeIntegralValuationTests
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Constructing the field needed for a domain-component pole

A nonintegral domain component has no original denominator in the scalar
kernel. Its original scalar localization is therefore a domain, and its
fraction field supplies an actual valuation witness without an assumed embedding.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.OriginalPrimeIntegralFiber
open ValuationSubringIntegralTests
variable {R B : Type*} [CommRing R] [CommRing B] [IsDomain B]
  (s : R →+* B) (P : Ideal R) [P.IsPrime]
local notation "T" => Localization (P.primeCompl.map s)
local notation "τ" => localizedMap s P

omit [IsDomain B] in
/-- Failure of local integrality excludes every original denominator from the scalar kernel. -/
theorem kernel_le_of_not_localized_integral (h : ¬ (τ).IsIntegral) : RingHom.ker s ≤ P := by
  intro a ha
  by_contra hn
  exact h (localizedMap_integral_of_kernel_scalar s P a hn ha)

/-- The localization of a nonintegral domain component is itself a domain. -/
theorem localization_domain_of_not_integral (h : ¬ (τ).IsIntegral) : IsDomain T := by
  apply IsLocalization.isDomain_localization
  rintro b ⟨a, ha, rfl⟩
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  intro hz
  exact ha (kernel_le_of_not_localized_integral s P h hz)

/-- A nonintegral coordinate constructs a valuation pole in the canonical fraction field. -/
theorem exists_fraction_valuation_pole (b : B)
    (h : ¬ (τ).IsIntegralElem (algebraMap B T b)) :
    let _ := localization_domain_of_not_integral s P (fun hi ↦ h (hi _))
    ∃ V : ValuationSubring (FractionRing T),
      ((algebraMap T (FractionRing T)).comp τ).range ≤ V.toSubring ∧
        algebraMap T (FractionRing T) (algebraMap B T b) ∉ V := by
  let _ := localization_domain_of_not_integral s P (fun hi ↦ h (hi _))
  apply exists_valuation_of_not_integral
  exact h.imp (RingHom.IsIntegralElem.map_iff (IsFractionRing.injective T (FractionRing T))).mp

/-- In particular, absence of an original avoiding equation constructs such a pole. -/
theorem exists_fraction_valuation_pole_of_no_equation (b : B)
    (h : ∀ p : Polynomial R, p.eval₂ s b = 0 → p.leadingCoeff ∈ P) :
    let hn : ¬ (τ).IsIntegral := fun hi ↦ by
      obtain ⟨p, hp, hlead⟩ := exists_equation_of_localized_integral s P b (hi _)
      exact hlead (h p hp)
    let _ := localization_domain_of_not_integral s P hn
    ∃ V : ValuationSubring (FractionRing T),
      ((algebraMap T (FractionRing T)).comp τ).range ≤ V.toSubring ∧
        algebraMap T (FractionRing T) (algebraMap B T b) ∉ V := by
  apply exists_fraction_valuation_pole s P b
  intro hi
  obtain ⟨p, hp, hlead⟩ := exists_equation_of_localized_integral s P b hi
  exact hlead (h p hp)

end FLT.Mazur.OriginalPrimeIntegralFiber
