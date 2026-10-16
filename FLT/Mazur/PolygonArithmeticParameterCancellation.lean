/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticStageCoefficients

/-!
# Cancel the arithmetic parameter after losing one quotient order

Multiplication by a nonzero parameter over a domain loses exactly one order.
Consequently division of a compatible smoothing system is unique at every
lower order, despite the nonuniqueness of division within one quotient.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonArithmeticStages
variable (R : Type*) [CommRing R] [IsDomain R] (π : R) (hπ : π ≠ 0) (m : ℕ)

include hπ

/-- A product vanishing one order higher has a factor vanishing at the lower order. -/
theorem restriction_eq_zero_of_parameter_mul_eq_zero
    (x : Quotient R π (m + 1)) (hx : parameter R π (m + 1) * x = 0) :
    restriction R π m x = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk _ π * Ideal.Quotient.mk _ a = 0 at hx
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, ideal,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨b, hb⟩ := hx
  have hab : a = π ^ (m + 1) * b := by
    apply mul_left_cancel₀ hπ
    calc
      π * a = π ^ (m + 1 + 1) * b := hb
      _ = π * (π ^ (m + 1) * b) := by rw [pow_succ']; ac_rfl
  change restriction R π m (algebraMap R _ a) = 0
  rw [AlgHom.commutes]
  change Ideal.Quotient.mk _ a = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, ideal, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  exact ⟨b, hab⟩

/-- Equal parameter multiples have equal restrictions one quotient order below. -/
theorem restriction_eq_of_parameter_mul_eq
    (x y : Quotient R π (m + 1))
    (hxy : parameter R π (m + 1) * x = parameter R π (m + 1) * y) :
    restriction R π m x = restriction R π m y := by
  have h := restriction_eq_zero_of_parameter_mul_eq_zero R π hπ m (x - y)
    (by rw [mul_sub, hxy, sub_self])
  rwa [map_sub, sub_eq_zero] at h

end FLT.Mazur.PolygonArithmeticStages
