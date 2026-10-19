/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.QuasiFiniteMinimalPrimeEquations
public import Mathlib.RingTheory.RingHom.FiniteType

/-!
# Construct finite local geometry on an original minimal-prime neighborhood

For fixed finite original generators, the constructed minimal-prime equations
supply one original principal neighborhood. At every prime of this neighborhood
the entire original localized algebra is finite. The same scalar and original
center are retained; no reduction or deletion of localized components is used.
This is local finiteness at all these primes, not yet a finite scheme restriction.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.OriginalPrimeIntegralFiber
open Polynomial
variable {R B : Type} [CommRing R] [CommRing B] [IsNoetherianRing R]
  (s : R →+* B) (P : PrimeSpectrum R)

/-- Exact minimal-prime equations construct one neighborhood with finite full local algebras. -/
theorem exists_finite_local_neighborhood_of_minimal
    (hP : P.asIdeal ∈ minimalPrimes R) (hs : s.QuasiFinite) (hf : s.FiniteType)
    {I : Type} [Finite I] (b : I → B)
    (hgen : Subring.closure (Set.range s ∪ Set.range b) = ⊤) :
    ∃ r : R, r ∉ P.asIdeal ∧ ∀ Q : PrimeSpectrum R, r ∉ Q.asIdeal →
      (localizedMap s Q.asIdeal).Finite := by
  classical
  let _ := Fintype.ofFinite I
  choose eqn heq hlead using fun i ↦ exists_equation_of_minimal_quasiFinite s P hP hs (b i)
  refine ⟨∏ i, (eqn i).leadingCoeff, ?_, ?_⟩
  · intro h
    obtain ⟨i, _, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hlead i hi
  · intro Q hQ
    have hi := localizedMap_integral_of_finite_equations s Q.asIdeal b eqn hgen heq hQ
    apply hi.to_finite
    exact RingHom.finiteType_isStableUnderBaseChange.isLocalization_map
      Q.asIdeal.primeCompl s hf

end FLT.Mazur.OriginalPrimeIntegralFiber
