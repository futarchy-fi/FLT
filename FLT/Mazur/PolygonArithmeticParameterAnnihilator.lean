/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRestrictionKernel

/-!
# Exact arithmetic parameter annihilators

For a nonzero parameter in an integral domain, cancellation identifies
the two complementary annihilators in each arithmetic coefficient ring.
These identities supply the exact coefficient layers needed for lifting
sections; no residue-field coefficient embedding is used.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (A : Type*) [CommRing A] [IsDomain A] (π : A) (hπ : π ≠ 0) (m : ℕ)

include hπ in
/-- Vanishing after multiplying by a parameter power is divisibility by its complement. -/
theorem parameter_pow_mul_mk_eq_zero_iff (k l : ℕ) (hkl : k + l = m + 1) (a : A) :
    parameter A π m ^ k * Ideal.Quotient.mk _ a = 0 ↔ π ^ l ∣ a := by
  change (Ideal.Quotient.mk _ π) ^ k * Ideal.Quotient.mk _ a = 0 ↔ _
  rw [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, ideal,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← hkl, pow_add,
    mul_dvd_mul_iff_left (pow_ne_zero k hπ)]

include hπ in
/-- The last parameter power kills exactly the parameter multiples. -/
theorem parameter_last_mul_eq_zero_iff (z : Quotient A π (m + 1)) :
    parameter A π (m + 1) ^ (m + 1) * z = 0 ↔
      ∃ w, parameter A π (m + 1) * w = z := by
  constructor
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    intro hz
    have ha := (parameter_pow_mul_mk_eq_zero_iff A π hπ (m + 1)
      (m + 1) 1 rfl a).mp hz
    rw [pow_one] at ha
    obtain ⟨b, rfl⟩ := ha
    exact ⟨Ideal.Quotient.mk _ b, (map_mul (Ideal.Quotient.mk _) π b).symm⟩
  · rintro ⟨w, rfl⟩
    rw [← mul_assoc, ← pow_succ, parameter_pow, zero_mul]

include hπ in
/-- The parameter kills exactly the original adjacent restriction kernel. -/
theorem parameter_mul_eq_zero_iff (z : Quotient A π (m + 1)) :
    parameter A π (m + 1) * z = 0 ↔ restriction A π m z = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [restriction_mk, Ideal.Quotient.eq_zero_iff_mem]
  change _ ↔ a ∈ Ideal.span {π} ^ (m + 1)
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  simpa only [pow_one] using
    parameter_pow_mul_mk_eq_zero_iff A π hπ (m + 1) 1 (m + 1) (by omega) a

end FLT.Mazur.PolygonArithmeticStages
