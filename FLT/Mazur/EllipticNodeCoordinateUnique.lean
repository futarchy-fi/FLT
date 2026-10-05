/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeCoordinateFactor

/-!
# Uniqueness of primitive nodal coordinates

Over a local domain with principal maximal ideal, a primitive pair fixes its
common depth and its quotients by a fixed uniformizer. This makes the depth
and tangent tests independent of the factorization witness.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]

/-- Dividing a coordinate of depth at least k+1 by πᵏ gives a nonunit. -/
theorem node_factor_mem_maximalIdeal {π a : R} (hπ : π ≠ 0)
    (hgen : maximalIdeal R = Ideal.span {π}) (k : ℕ)
    (h : π ^ k * a ∈ maximalIdeal R ^ (k + 1)) : a ∈ maximalIdeal R := by
  obtain ⟨b, hb, he⟩ := exists_node_deep_factor hgen k h
  exact mul_left_cancel₀ (pow_ne_zero k hπ) he ▸ hb

/-- A primitive pair has exact common depth k. -/
theorem node_primitive_not_deeper {π a b : R} (hπ : π ≠ 0)
    (hgen : maximalIdeal R = Ideal.span {π}) (k : ℕ) (hprim : IsUnit a ∨ IsUnit b) :
    ¬ (π ^ k * a ∈ maximalIdeal R ^ (k + 1) ∧
      π ^ k * b ∈ maximalIdeal R ^ (k + 1)) := by
  rintro ⟨ha, hb⟩
  rcases hprim with h | h
  · exact node_factor_mem_maximalIdeal hπ hgen k ha h
  · exact node_factor_mem_maximalIdeal hπ hgen k hb h

/-- Comparing with another common factor bounds the depth by that of a primitive pair. -/
theorem node_common_depth_le {π a b c d : R} (hπ : π ≠ 0)
    (hgen : maximalIdeal R = Ideal.span {π}) {k l : ℕ} (hprim : IsUnit a ∨ IsUnit b)
    (hx : π ^ k * a = π ^ l * c) (hy : π ^ k * b = π ^ l * d) : l ≤ k := by
  by_contra h
  have hπm : π ∈ maximalIdeal R := hgen ▸ Ideal.mem_span_singleton_self π
  have hp : π ^ l ∈ maximalIdeal R ^ (k + 1) :=
    Ideal.pow_le_pow_right (by omega) (Ideal.pow_mem_pow hπm l)
  apply node_primitive_not_deeper hπ hgen k hprim
  exact ⟨hx ▸ (maximalIdeal R ^ (k + 1)).mul_mem_right c hp,
    hy ▸ (maximalIdeal R ^ (k + 1)).mul_mem_right d hp⟩

/-- Two primitive factorizations using the same uniformizer agree in every coordinate. -/
theorem node_primitive_coordinates_unique {π a b c d : R} (hπ : π ≠ 0)
    (hgen : maximalIdeal R = Ideal.span {π}) {k l : ℕ}
    (hab : IsUnit a ∨ IsUnit b) (hcd : IsUnit c ∨ IsUnit d)
    (hx : π ^ k * a = π ^ l * c) (hy : π ^ k * b = π ^ l * d) :
    k = l ∧ a = c ∧ b = d := by
  have hk := le_antisymm (node_common_depth_le hπ hgen hcd hx.symm hy.symm)
    (node_common_depth_le hπ hgen hab hx hy)
  subst l
  exact ⟨rfl, mul_left_cancel₀ (pow_ne_zero k hπ) hx,
    mul_left_cancel₀ (pow_ne_zero k hπ) hy⟩

end FLT.Mazur
