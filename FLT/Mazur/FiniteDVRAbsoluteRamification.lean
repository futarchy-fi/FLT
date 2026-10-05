/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudFiniteValuation
public import FLT.Mathlib.RingTheory.DiscreteValuationRing.TotalRamification

/-!
# Absolute ramification over an unramified DVR

If the residue prime is a uniformizer of the base, its order upstairs is
the actual relative ramification index. This turns the degree-six bound
into the strict absolute bound required by finite-flat rigidity.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing IsDiscreteValuationRing

variable {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [Module.Finite R S] [FaithfulSMul R S]

/-- Over an unramified base, the relative index is the absolute order of the prime. -/
theorem prime_order_eq_relative_ramification (p : ℕ) (hp : Irreducible (p : R)) :
    RaynaudParameters.order (p : S) = (maximalIdeal S).ramificationIdx R := by
  have h := addValMapUniformizerEqRamificationIdx (S := S) hp
  simpa [RaynaudParameters.order] using congrArg ENat.toNat h

/-- A degree-six ramification bound is small enough for primes at least seventeen. -/
theorem prime_order_lt_of_ramification_le_six (p : ℕ) (hp : Irreducible (p : R))
    (he : (maximalIdeal S).ramificationIdx R ≤ 6) (hp17 : 17 ≤ p) :
    RaynaudParameters.order (p : S) < p - 1 := by
  rw [prime_order_eq_relative_ramification (S := S) p hp]
  omega

end FLT.Mazur
