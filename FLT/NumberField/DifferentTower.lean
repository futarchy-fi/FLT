/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.IdealMultiplicityMap
public import FLT.NumberField.DifferentExponentBounds

/-!
# Different exponents in towers of number fields

The ideal-theoretic tower formula gives the usual formula for primewise
different exponents. In particular an unramified extension preserves the
absolute different exponent at each nonzero prime.
-/

@[expose] public noncomputable section

open UniqueFactorizationMonoid

namespace NumberField

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] FractionRing.liftAlgebra

/-- The absolute different exponent is the relative exponent plus the
ramification index times the absolute exponent in the base field. -/
theorem differentExponentAt_tower
    (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥) :
    differentExponentAt L P =
      (normalizedFactors (differentIdeal (𝓞 K) (𝓞 L))).count P +
        P.ramificationIdx (𝓞 K) * differentExponentAt K (P.under (𝓞 K)) := by
  classical
  have hQ : P.under (𝓞 K) ≠ ⊥ := Ideal.under_ne_bot _ hP
  have hmap : (differentIdeal ℤ (𝓞 K)).map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot
  rw [differentExponentAt,
    differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 K) (𝓞 L),
    normalizedFactors_mul differentIdeal_ne_bot hmap, Multiset.count_add,
    Ideal.count_normalizedFactors_map P hQ _ differentIdeal_ne_bot]
  rfl

/-- An extension unramified at `P` preserves its absolute different exponent. -/
theorem differentExponentAt_eq_of_isUnramifiedAt
    (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥)
    [Algebra.IsUnramifiedAt (𝓞 K) P] :
    differentExponentAt L P = differentExponentAt K (P.under (𝓞 K)) := by
  classical
  have hz : (normalizedFactors (differentIdeal (𝓞 K) (𝓞 L))).count P = 0 := by
    apply Multiset.count_eq_zero.mpr
    intro h
    exact (not_dvd_differentIdeal_iff.mpr
      (inferInstance : Algebra.IsUnramifiedAt (𝓞 K) P)) (dvd_of_mem_normalizedFactors h)
  rw [differentExponentAt_tower K L P hP, hz,
    Ideal.ramificationIdx_eq_one P (𝓞 K), one_mul, zero_add]

end NumberField
