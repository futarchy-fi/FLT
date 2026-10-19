/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeMinimalPrimeFinitePullback
public import FLT.Mazur.OriginalPrimeIntegralEquations

/-!
# Exact original equations at minimal scalar primes

Quasi-finiteness over a Noetherian original scalar ring constructs finiteness
at every original minimal prime. The existing denominator construction then
produces polynomial equations in the unchanged source ring, with leading
coefficients outside that same prime. No reducedness or integrality input is used.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.OriginalPrimeIntegralFiber
open Polynomial
variable {R B : Type} [CommRing R] [CommRing B] [IsNoetherianRing R]
  (s : R →+* B) (P : PrimeSpectrum R)
local notation "T" => Localization (P.asIdeal.primeCompl.map s)
local notation "L" => Localization.AtPrime P.asIdeal
local notation "τ" => localizedMap s P.asIdeal

/-- Quasi-finiteness constructs finite local geometry at the unchanged original minimal prime. -/
theorem localizedMap_finite_of_minimal_quasiFinite
    (hP : P.asIdeal ∈ minimalPrimes R) (hs : s.QuasiFinite) : (τ).Finite := by
  have hq : (τ).QuasiFinite :=
    RingHom.QuasiFinite.isStableUnderBaseChange.isLocalization_map P.asIdeal.primeCompl s hs
  let _ := (τ).toAlgebra
  let _ : Algebra.QuasiFinite L T := hq
  let _ := SchemeMinimalPrimeFinitePullback.localization_isArtinian P hP
  let _ : Module.Finite L T := Module.Finite.of_quasiFinite
  exact RingHom.finite_algebraMap.mpr inferInstance

/-- Each original element has an exact equation whose leading coefficient avoids the same prime. -/
theorem exists_equation_of_minimal_quasiFinite
    (hP : P.asIdeal ∈ minimalPrimes R) (hs : s.QuasiFinite) (b : B) :
    ∃ p : R[X], p.eval₂ s b = 0 ∧ p.leadingCoeff ∉ P.asIdeal := by
  exact exists_equation_of_localized_integral s P.asIdeal b
    ((localizedMap_finite_of_minimal_quasiFinite s P hP hs).to_isIntegral _)

/-- Empty original minimal fibers supply an exact kernel scalar from quasi-finiteness alone. -/
theorem exists_kernel_scalar_of_minimal_quasiFinite
    (hP : P.asIdeal ∈ minimalPrimes R) (hs : s.QuasiFinite)
    (he : ∀ Q : PrimeSpectrum B, Q.asIdeal.comap s ≠ P.asIdeal) :
    ∃ r : R, r ∉ P.asIdeal ∧ s r = 0 :=
  exists_kernel_scalar s P.asIdeal
    (localizedMap_finite_of_minimal_quasiFinite s P hP hs).to_isIntegral he

end FLT.Mazur.OriginalPrimeIntegralFiber
