/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticTypeIIIDepth
public import FLT.Mazur.EllipticNodeCoordinateUnique

/-!
# Refining additive coefficient depths

For a principal maximal ideal in a local domain, a square has depth at
least three exactly when its base has depth at least two. This upgrades
the failed type III b₈ test to the a₄ depth needed by the later branches.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]

/-- Over a principal local domain, a square lies in m³ exactly when its base lies in m². -/
theorem square_mem_cube_iff_mem_square {π x : R} (hπ : π ≠ 0)
    (hgen : maximalIdeal R = Ideal.span {π}) :
    x ^ 2 ∈ maximalIdeal R ^ 3 ↔ x ∈ maximalIdeal R ^ 2 := by
  have hs {a : R} (ha : a ^ 2 ∈ maximalIdeal R) : a ∈ maximalIdeal R := by
    apply (residue_eq_zero_iff _).mp
    have he := (residue_eq_zero_iff _).mpr ha
    rw [map_pow] at he
    exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp he
  constructor
  · intro hx
    have hm := hs (Ideal.pow_le_self (by decide : 3 ≠ 0) hx)
    obtain ⟨a, ha⟩ := exists_node_coordinate_factor hgen 1 (by simpa using hm)
    simp only [pow_one] at ha
    have hsq : π ^ 2 * a ^ 2 ∈ maximalIdeal R ^ 3 := by simpa [ha, mul_pow] using hx
    have ham := hs (node_factor_mem_maximalIdeal hπ hgen 2 hsq)
    rw [ha, pow_two]
    exact Ideal.mul_mem_mul (hgen ▸ Ideal.mem_span_singleton_self π) ham
  · intro hx
    have he : x ^ 2 ∈ maximalIdeal R ^ 4 := by
      simpa only [← pow_mul] using Ideal.pow_mem_pow hx 2
    exact Ideal.pow_le_pow_right (by decide : 3 ≤ 4) he

/-- Under the early additive tests, the b₈ depth test is equivalent to the a₄ depth test. -/
theorem b8_mem_cube_iff_a4_mem_square (W : WeierstrassCurve R) {π : R}
    (hπ : π ≠ 0) (hgen : maximalIdeal R = Ideal.span {π})
    (h1 : W.a₁ ∈ maximalIdeal R) (h2 : W.a₂ ∈ maximalIdeal R)
    (h3 : W.a₃ ∈ maximalIdeal R) (h4 : W.a₄ ∈ maximalIdeal R)
    (h6 : W.a₆ ∈ maximalIdeal R ^ 2) :
    W.b₈ ∈ maximalIdeal R ^ 3 ↔ W.a₄ ∈ maximalIdeal R ^ 2 := by
  have he := b8_add_a4_sq_mem_cube W (maximalIdeal R) h1 h2 h3 h4 h6
  constructor
  · intro h8
    apply (square_mem_cube_iff_mem_square hπ hgen).mp
    simpa only [add_sub_cancel_left] using (maximalIdeal R ^ 3).sub_mem he h8
  · intro h4'
    have hs := (square_mem_cube_iff_mem_square hπ hgen).mpr h4'
    simpa only [add_sub_cancel_right] using (maximalIdeal R ^ 3).sub_mem he hs

end FLT.Mazur
