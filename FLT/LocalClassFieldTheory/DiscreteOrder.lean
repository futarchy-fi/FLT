/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Integer order on the fraction field of a DVR

The maximal-ideal adic valuation defines the classical integer order. Its
normalization is zero on integral units and one on a uniformizer.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing IsDedekindDomain

variable (S L : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra S L] [IsFractionRing S L]

/-- The unique height-one prime of a DVR. -/
def dvrPrime : HeightOneSpectrum S :=
  ⟨maximalIdeal S, inferInstance, IsDiscreteValuationRing.not_a_field S⟩

/-- The integer order on nonzero elements of the fraction field. -/
def discreteOrder : Lˣ →* Multiplicative ℤ where
  toFun u := Multiplicative.ofAdd (-WithZero.log ((dvrPrime S).valuation L (u : L)))
  map_one' := by simp
  map_mul' u v := by
    have hu : (dvrPrime S).valuation L (u : L) ≠ 0 := by simp
    have hv : (dvrPrime S).valuation L (v : L) ≠ 0 := by simp
    simp [map_mul, WithZero.log_mul hu hv, mul_comm]

/-- Integral units have order zero. -/
@[simp] theorem discreteOrder_unit (u : Sˣ) :
    discreteOrder S L (Units.map (algebraMap S L) u) = 1 := by
  have h : (dvrPrime S).valuation L (algebraMap S L (u : S)) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem (dvrPrime S)).2 (by
      change (u : S) ∉ maximalIdeal S
      exact fun h => h u.isUnit)
  simp [discreteOrder, h]

/-- A uniformizer has positive order one. -/
theorem discreteOrder_uniformizer {π : S} (hπ : Irreducible π) :
    discreteOrder S L (Units.mk0 (algebraMap S L π)
      (by simpa using (IsFractionRing.injective S L).ne hπ.ne_zero)) =
      Multiplicative.ofAdd 1 := by
  have hv : (dvrPrime S).valuation L (algebraMap S L π) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_singleton _ hπ.ne_zero hπ.maximalIdeal_eq
  simp [discreteOrder, hv]

end LocalClassFieldTheory
