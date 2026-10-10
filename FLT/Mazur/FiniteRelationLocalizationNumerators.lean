/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationLocalizationKernels

/-!
# Numerators of relations on principal opens

A localized element vanishing in the full quotient is a unit multiple of a
numerator belonging to the original relation ideal. Clearing denominators both
before and after projection is needed when the original quotient has torsion.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationLocalization

universe u v

variable (R : Type u) [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P) (r : P)

/-- A vanishing localized section has a numerator in the full relation ideal. -/
theorem exists_relation_numerator (s : Finset I) (x : Stage I r s)
    (hx : toQuotient R I r s x = 0) :
    ∃ (z : I) (n : ℕ), numerator I r s z = x * numerator I r s r ^ n := by
  let d := Ideal.Quotient.mk (FiniteRelationModel.relations I s) r
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj d x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have he : algebraMap (P ⧸ I) (Quotient I r) (Ideal.Quotient.mk I p) = 0 := by
    have hh := congrArg (toQuotient R I r s) ha
    rw [map_mul, hx, zero_mul, toQuotient_algebraMap] at hh
    exact hh.symm
  obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq (Ideal.Quotient.mk I r)
    (he.trans (map_zero _).symm)
  have hz : r ^ m * p ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul, map_pow, mul_zero] using hm
  refine ⟨⟨r ^ m * p, hz⟩, n + m, ?_⟩
  change numerator I r s (r ^ m * p) = x * numerator I r s r ^ (n + m)
  have hp : numerator I r s p = x * numerator I r s r ^ n := ha.symm
  rw [map_mul, map_pow, hp, pow_add]
  ring

/-- The denominator remains a unit at every stage. -/
theorem numerator_denominator_isUnit (s : Finset I) : IsUnit (numerator I r s r) :=
  IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk (FiniteRelationModel.relations I s) r)

/-- A numerator representing a unit multiple belongs to exactly the same ideals. -/
theorem numerator_mem_iff (s : Finset I) (J : Ideal (Stage I r s))
    (x : Stage I r s) (z : I) (n : ℕ)
    (h : numerator I r s z = x * numerator I r s r ^ n) :
    numerator I r s z ∈ J ↔ x ∈ J := by
  rw [h]
  exact J.mul_unit_mem_iff_mem ((numerator_denominator_isUnit I r s).pow n)

end FLT.Mazur.FiniteRelationLocalization
