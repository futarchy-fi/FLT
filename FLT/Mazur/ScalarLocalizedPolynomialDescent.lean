/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarLocalPolynomialTests
public import Mathlib.RingTheory.Localization.Integral

/-!
# Exact scalar equations from localized scalar coefficients

Clearing a polynomial over a scalar localization preserves separability in
any residue field to which that localization maps. The resulting polynomial
has coefficients in the original scalar ring and vanishes in the full source
stalk, so nilpotent structure is retained.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarLocalizedPolynomialDescent
open Polynomial
variable {R T A B K : Type} [CommRing R] [CommRing T] [CommRing A]
  [CommRing B] [CommRing K] [Algebra R T] (M : Submonoid R) [IsLocalization M T]

/-- Clearing scalar denominators preserves separability after any map from the localization. -/
theorem separable_integerNormalization (μ : T →+* K) (F : T[X])
    (hF : (F.map μ).Separable) :
    ((IsLocalization.integerNormalization M F).map
      (μ.comp (algebraMap R T))).Separable := by
  obtain ⟨b, hb, he⟩ := IsLocalization.integerNormalization_spec M F
  rw [← Polynomial.map_map, he, ← IsScalarTower.algebraMap_smul T b F,
    smul_eq_C_mul, Polynomial.map_mul, map_C]
  exact Separable.unit_mul
    (isUnit_C.mpr ((IsLocalization.map_units T ⟨b, hb⟩).map μ)) hF

/-- A localized coefficient equation descends to the exact scalar ring in the full source stalk. -/
theorem equation_integerNormalization (σ : R →+* A) (φ : A →+* B)
    (Q : PrimeSpectrum B) (z : A) (F : T[X])
    (ψ : T →+* Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
    (μ : T →+* Q.asIdeal.ResidueField)
    (hψ : ψ.comp (algebraMap R T) =
      (algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)).comp σ)
    (hμ : μ.comp (algebraMap R T) =
      ((algebraMap B Q.asIdeal.ResidueField).comp φ).comp σ)
    (hz : F.eval₂ ψ
      (algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal) z) = 0)
    (hs : (F.map μ).Separable) :
    ScalarLocalPolynomialTests.Equation σ φ Q z
      (IsLocalization.integerNormalization M F) := by
  constructor
  · rw [hom_eval₂]
    rw [← hψ]
    exact IsLocalization.integerNormalization_eval₂_eq_zero M ψ F hz
  · rw [← hμ]
    exact separable_integerNormalization M μ F hs

end FLT.Mazur.ScalarLocalizedPolynomialDescent
