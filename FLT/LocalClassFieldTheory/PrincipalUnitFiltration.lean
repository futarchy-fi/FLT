/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Principal units and their coefficients

The n-th principal units are the kernel of reduction modulo the n-th power
of a chosen element. In a domain their divided difference from 1 is unique.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

variable {R : Type*} [CommRing R]

/-- Units congruent to 1 modulo `π ^ n`. -/
def principalUnits (π : R) (n : ℕ) : Subgroup Rˣ :=
  (Units.map (Ideal.Quotient.mk (Ideal.span {π ^ n})).toMonoidHom).ker

/-- Membership is divisibility of the difference from 1. -/
theorem mem_principalUnits (π : R) (n : ℕ) (u : Rˣ) :
    u ∈ principalUnits π n ↔ π ^ n ∣ (u : R) - 1 := by
  change Units.map _ u = 1 ↔ _
  rw [Units.ext_iff]
  change Ideal.Quotient.mk _ (u : R) = 1 ↔ _
  rw [← map_one (Ideal.Quotient.mk (Ideal.span {π ^ n})),
    Ideal.Quotient.eq, Ideal.mem_span_singleton]

/-- The filtration decreases as the exponent increases. -/
theorem principalUnits_antitone (π : R) : Antitone (principalUnits π) := by
  intro n m h u hu
  exact (mem_principalUnits π n u).2
    ((pow_dvd_pow π h).trans ((mem_principalUnits π m u).1 hu))

/-- The coefficient after dividing `u - 1` by `π ^ n`. -/
def principalCoeff (π : R) (n : ℕ) (u : principalUnits π n) : R :=
  Classical.choose ((mem_principalUnits π n u).1 u.property)

/-- The defining equality for the divided difference. -/
theorem principalCoeff_spec (π : R) (n : ℕ) (u : principalUnits π n) :
    (u.val : R) - 1 = π ^ n * principalCoeff π n u :=
  Classical.choose_spec ((mem_principalUnits π n u).1 u.property)

variable [IsDomain R] {π : R}

/-- Division by a nonzero power makes the coefficient unique. -/
theorem principalCoeff_eq (hπ : π ≠ 0) (n : ℕ) (u : principalUnits π n)
    (a : R) (ha : (u.val : R) - 1 = π ^ n * a) : principalCoeff π n u = a :=
  mul_left_cancel₀ (pow_ne_zero n hπ) ((principalCoeff_spec π n u).symm.trans ha)

/-- Multiplication of units has a quadratic error in its coefficient. -/
theorem principalCoeff_mul (hπ : π ≠ 0) (n : ℕ) (u v : principalUnits π n) :
    principalCoeff π n (u * v) = principalCoeff π n u + principalCoeff π n v +
      π ^ n * principalCoeff π n u * principalCoeff π n v := by
  apply principalCoeff_eq hπ
  have hu := principalCoeff_spec π n u
  have hv := principalCoeff_spec π n v
  change (u.val : R) * (v.val : R) - 1 = _
  calc
    _ = ((u.val : R) - 1) + ((v.val : R) - 1) +
        ((u.val : R) - 1) * ((v.val : R) - 1) := by ring
    _ = _ := by rw [hu, hv]; ring

/-- One step deeper is precisely divisibility of the coefficient by `π`. -/
theorem principalCoeff_dvd_iff (hπ : π ≠ 0) (n : ℕ) (u : principalUnits π n) :
    π ∣ principalCoeff π n u ↔ u.val ∈ principalUnits π (n + 1) := by
  rw [mem_principalUnits, principalCoeff_spec, pow_succ]
  exact (mul_dvd_mul_iff_left (pow_ne_zero n hπ)).symm

end LocalClassFieldTheory
