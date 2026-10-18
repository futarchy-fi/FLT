/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalPrimeIntegralEquations
public import FLT.Mazur.ValuationSubringIntegralTests

/-!
# Valuation tests after embedding an original localization in a field

For a domain component, an embedding of its scalar localization into a field
turns the fixed generator equations into valuation-subring tests. Failure
constructs a pole. Its original center is a generization of the chosen prime;
no equality of centers is asserted.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.OriginalPrimeIntegralFiber
open ValuationSubringIntegralTests
variable {R B K : Type*} [CommRing R] [CommRing B] [Field K]
  (s : R →+* B) (P : Ideal R) [P.IsPrime]
local notation "T" => Localization (P.primeCompl.map s)
local notation "L" => Localization.AtPrime P
local notation "τ" => localizedMap s P
variable (φ : Localization (P.primeCompl.map s) →+* K) (hφ : Function.Injective φ) (S : Set B)
  (hgen : Subring.closure (Set.range s ∪ S) = ⊤)

include hφ hgen in
/-- The original generators need only be tested in valuation subrings of one ambient field. -/
theorem localizedMap_integral_iff_generator_valuations :
    (τ).IsIntegral ↔ ∀ V : ValuationSubring K,
      (φ.comp τ).range ≤ V.toSubring → ∀ b ∈ S, φ (algebraMap B T b) ∈ V := by
  refine ⟨fun h V hV b _ ↦ ?_, fun h ↦ ?_⟩
  · exact (integralElem_iff_valuation_subrings _ _).mp ((h _).map φ) V hV
  · apply localizedMap_integral_of_generator_equations s P S hgen
    intro b hb
    apply exists_equation_of_localized_integral
    apply RingHom.IsIntegralElem.of_map hφ
    exact (integralElem_iff_valuation_subrings _ _).mpr (fun V hV ↦ h V hV b hb)

include hφ hgen in
/-- Nonintegrality constructs a pole of an unchanged original generator. -/
theorem exists_generator_valuation_obstruction (h : ¬ (τ).IsIntegral) :
    ∃ V : ValuationSubring K, (φ.comp τ).range ≤ V.toSubring ∧
      ∃ b ∈ S, φ (algebraMap B T b) ∉ V := by
  classical
  simpa only [not_forall, not_imp, exists_prop] using
    h.imp (localizedMap_integral_iff_generator_valuations s P φ hφ S hgen).mpr

/-- Restrict the actual localized scalar image to a containing valuation subring. -/
def valuationScalarMap (V : ValuationSubring K) (hV : (φ.comp τ).range ≤ V.toSubring) :
    L →+* V :=
  (φ.comp τ).codRestrict V.toSubring (fun a ↦ hV ⟨a, rfl⟩)

/-- This valuation's original scalar center lies below the original prime. -/
theorem valuationScalarMap_center_le (V : ValuationSubring K)
    (hV : (φ.comp τ).range ≤ V.toSubring) :
    (IsLocalRing.maximalIdeal V).comap
      ((valuationScalarMap s P φ V hV).comp (algebraMap R L)) ≤ P := by
  intro a ha
  by_contra hn
  change ¬ IsUnit (valuationScalarMap s P φ V hV (algebraMap R L a)) at ha
  have hu := IsLocalization.map_units (M := P.primeCompl) L ⟨a, hn⟩
  exact ha (hu.map (valuationScalarMap s P φ V hV))

/-- The induced valuation scalars retain the original coefficient square. -/
theorem valuationScalarMap_original_square (V : ValuationSubring K)
    (hV : (φ.comp τ).range ≤ V.toSubring) :
    (V.subtype.comp (valuationScalarMap s P φ V hV)).comp (algebraMap R L) =
      φ.comp ((algebraMap B T).comp s) := by
  change (φ.comp τ).comp (algebraMap R L) = _
  rw [RingHom.comp_assoc, localizedMap_comp]

/-- A scalar in the exact kernel outside the original prime makes local integrality automatic. -/
theorem localizedMap_integral_of_kernel_scalar (a : R) (ha : a ∉ P) (hs : s a = 0) :
    (τ).IsIntegral := by
  apply localizedMap_integral_of_numerators
  intro b
  apply (localized_integral_iff_equation s P b).mpr
  exact ⟨Polynomial.C a, by simpa only [Polynomial.eval₂_C] using hs,
    by simpa only [Polynomial.leadingCoeff_C] using ha⟩

end FLT.Mazur.OriginalPrimeIntegralFiber
