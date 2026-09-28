/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Prime multiplicities under extension of ideals

Extending a nonzero ideal between Dedekind domains multiplies its multiplicity
at the contracted prime by the ramification index. Extracting the prime power
before mapping avoids any assumption that the extension is Galois.
-/

@[expose] public noncomputable section

open UniqueFactorizationMonoid

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S]
  [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S]
  [Module.IsTorsionFree R S]

/-- The multiplicity of a prime in an extended ideal is the original multiplicity
multiplied by the ramification index. -/
theorem count_normalizedFactors_map
    (P : Ideal S) [P.IsPrime] (hP : P.under R ≠ ⊥)
    (I : Ideal R) (hI : I ≠ ⊥) :
    (normalizedFactors (I.map (algebraMap R S))).count P =
      P.ramificationIdx R * (normalizedFactors I).count (P.under R) := by
  classical
  have hprime := Ideal.prime_of_isPrime hP inferInstance
  obtain ⟨J, hJ, hndvd⟩ :=
    (FiniteMultiplicity.of_prime_left hprime hI).exists_eq_pow_mul_and_not_dvd
  rw [multiplicity_eq_count_normalizedFactors hprime.irreducible hI,
    normalize_eq] at hJ
  have hJ0 : J ≠ ⊥ := by
    intro h
    apply hndvd
    rw [h]
    exact dvd_zero _
  have hmapJ : J.map (algebraMap R S) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hJ0
  have hmapP : (P.under R).map (algebraMap R S) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hP
  have hcountJ : (normalizedFactors (J.map (algebraMap R S))).count P = 0 := by
    apply Multiset.count_eq_zero.mpr
    intro h
    apply hndvd
    rw [Ideal.dvd_iff_le]
    exact Ideal.map_le_iff_le_comap.mp
      (Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors h))
  have he := Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
    (P.under R) P hmapP
  conv_lhs => rw [hJ]
  rw [Ideal.map_mul, Ideal.map_pow,
    normalizedFactors_mul (pow_ne_zero _ hmapP) hmapJ,
    Multiset.count_add, normalizedFactors_pow, Multiset.count_nsmul,
    hcountJ, add_zero, ← he, Nat.mul_comm]

end Ideal
