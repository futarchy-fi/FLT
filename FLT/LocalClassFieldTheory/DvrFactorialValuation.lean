/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.DiscreteOrder
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Local valuations of natural numbers and factorials

After removing the residue-characteristic prime power from a natural
number, the remaining factor is an integral unit. This computes the
actual DVR valuation and bounds factorial denominators geometrically.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing IsDedekindDomain

variable (S L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra S L] [IsFractionRing S L]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]

/-- The prime-free part of a nonzero natural number is a unit in the local ring. -/
theorem dvr_natCast_primeFree_unit (n : ℕ) (hn : n ≠ 0) :
    IsUnit (Nat.divMaxPow n p : S) := by
  apply notMem_maximalIdeal.mp
  rw [← residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero_iff (ResidueField S) p]
  exact Nat.not_dvd_divMaxPow (Fact.out : p.Prime).one_lt hn

/-- The actual local valuation of n is the valuation of p to the p-adic exponent of n. -/
theorem dvr_valuation_natCast (n : ℕ) (hn : n ≠ 0) :
    (dvrPrime S).valuation L (n : L) =
      ((dvrPrime S).valuation L (p : L)) ^ padicValNat p n := by
  have hu : (dvrPrime S).valuation L (Nat.divMaxPow n p : L) = 1 := by
    rw [← map_natCast (algebraMap S L)]
    apply (HeightOneSpectrum.valuation_eq_one_iff_notMem (dvrPrime S)).mpr
    exact notMem_maximalIdeal.mpr (dvr_natCast_primeFree_unit S p n hn)
  have h : (n : L) = (p : L) ^ padicValNat p n * (Nat.divMaxPow n p : L) := by
    simpa only [Nat.cast_mul, Nat.cast_pow] using
      congrArg (fun m : ℕ => (m : L)) (Nat.pow_padicValNat_mul_divMaxPow p n).symm
  rw [h, map_mul, map_pow, hu, mul_one]

/-- Factorials have their exact local valuation, with no denominator estimate assumed. -/
theorem dvr_valuation_factorial (n : ℕ) :
    (dvrPrime S).valuation L (n.factorial : L) =
      ((dvrPrime S).valuation L (p : L)) ^ padicValNat p n.factorial :=
  dvr_valuation_natCast S L p n.factorial n.factorial_ne_zero

/-- The factorial valuation is bounded below by the nth power of the residue prime's value. -/
theorem dvr_valuation_factorial_lower (n : ℕ) :
    ((dvrPrime S).valuation L (p : L)) ^ n ≤ (dvrPrime S).valuation L (n.factorial : L) := by
  rw [dvr_valuation_factorial S L p]
  apply pow_le_pow_right_of_le_one' _ (padicValNat_factorial_le p n)
  rw [← map_natCast (algebraMap S L)]
  exact HeightOneSpectrum.valuation_le_one (dvrPrime S) (p : S)

end LocalClassFieldTheory
