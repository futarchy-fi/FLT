/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginIdeal

/-!
# Parameter division and exact orders at the original zero section

Every function on the original parameter neighborhood is its value at zero
plus a parameter multiple. Regularity detects the next power without losing
nilpotent coefficients of the base.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Vanishing on the actual zero section is precisely divisibility by its regular parameter. -/
theorem originEvaluation_eq_zero_iff (a : OriginNeighborhood W) :
    originEvaluation W a = 0 ↔ originCoordinate W 0 ∣ a := by
  change a ∈ RingHom.ker (originEvaluation W).toRingHom ↔ _
  rw [originEvaluation_kernel, Ideal.mem_span_singleton]

/-- Divide an actual regular function into its original base value and a parameter multiple. -/
theorem originParameter_division (a : OriginNeighborhood W) :
    ∃ b : OriginNeighborhood W,
      a = algebraMap R _ (originEvaluation W a) + originCoordinate W 0 * b := by
  have hz : originEvaluation W (a - algebraMap R _ (originEvaluation W a)) = 0 := by
    simp
  obtain ⟨b, hb⟩ := (originEvaluation_eq_zero_iff W _).mp hz
  exact ⟨b, by linear_combination hb⟩

/-- Cancellation of the original regular parameter detects each successive order. -/
theorem originParameter_order_step (a : OriginNeighborhood W) (n : ℕ) :
    originCoordinate W 0 ^ n * a ∈ Ideal.span {originCoordinate W 0 ^ (n + 1)} ↔
      originEvaluation W a = 0 := by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨b, hb⟩
    have ha : a = originCoordinate W 0 * b := by
      apply ((originCoordinate_x_regular W).pow n).left
      simpa only [pow_succ, mul_assoc] using hb
    rw [ha, map_mul, originEvaluation_x, zero_mul]
  · intro ha
    obtain ⟨b, hb⟩ := (originEvaluation_eq_zero_iff W a).mp ha
    exact ⟨b, by rw [hb, pow_succ, mul_assoc]⟩

/-- Even a nonzero nilpotent base coefficient survives in its exact parameter degree. -/
theorem originParameter_scalar_order (r : R) (n : ℕ) :
    originCoordinate W 0 ^ n * algebraMap R _ r ∈
      Ideal.span {originCoordinate W 0 ^ (n + 1)} ↔ r = 0 := by
  rw [originParameter_order_step]
  simp

/-- The leading base coefficient is unique modulo the next parameter power. -/
theorem originParameter_leading_unique (r s : R) (n : ℕ)
    (h : originCoordinate W 0 ^ n * algebraMap R _ r -
      originCoordinate W 0 ^ n * algebraMap R _ s ∈
        Ideal.span {originCoordinate W 0 ^ (n + 1)}) : r = s := by
  apply sub_eq_zero.mp
  apply (originParameter_scalar_order W (r - s) n).mp
  simpa only [map_sub, mul_sub] using h

end FLT.Mazur.WeierstrassIntegralChart
