/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticStarDeepCoordinates
public import FLT.Mazur.EllipticAdditiveDepthRefinement
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# Deepening the triple-root branch after the type IV* test

An actual point supplies a y-translation that puts a₆ in m⁵. If b₆ also
lies in m⁵, the translated a₃ lies in m³. The construction works in residue
characteristic two and does not assume a square root in the residue field.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

/-- A square has depth at least five exactly when its base has depth at least three. -/
theorem square_mem_fifth_iff_mem_cube {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    {π x : R} (hπ : π ≠ 0) (hgen : maximalIdeal R = Ideal.span {π}) :
    x ^ 2 ∈ maximalIdeal R ^ 5 ↔ x ∈ maximalIdeal R ^ 3 := by
  constructor
  · intro hx
    have hx2 := (square_mem_cube_iff_mem_square hπ hgen).mp
      (Ideal.pow_le_pow_right (by decide : 3 ≤ 5) hx)
    obtain ⟨a, ha⟩ := exists_node_coordinate_factor hgen 2 hx2
    have hs : π ^ 4 * a ^ 2 ∈ maximalIdeal R ^ 5 := by
      simpa only [ha, mul_pow, ← pow_mul] using hx
    have hm := node_factor_mem_maximalIdeal hπ hgen 4 hs
    have ham : a ∈ maximalIdeal R := (residue_eq_zero_iff _).mp
      ((pow_eq_zero_iff (by decide : 2 ≠ 0)).mp
        (by simpa only [map_pow] using (residue_eq_zero_iff _).mpr hm))
    rw [ha, pow_succ]
    exact Ideal.mul_mem_mul
      (Ideal.pow_mem_pow (hgen ▸ Ideal.mem_span_singleton_self π) 2) ham
  · intro hx
    have hs : x ^ 2 ∈ maximalIdeal R ^ 6 := by
      simpa only [← pow_mul] using Ideal.pow_mem_pow hx 2
    exact Ideal.pow_le_pow_right (by decide : 5 ≤ 6) hs

/-- A point with both coordinates in I² deepens the y-translated constant coefficient. -/
theorem star_translated_a6_mem_fifth {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (I : Ideal R) {x y : R}
    (he : W.toAffine.Equation x y) (h1 : W.a₁ ∈ I) (h2 : W.a₂ ∈ I ^ 2)
    (h4 : W.a₄ ∈ I ^ 3) (hx : x ∈ I ^ 2) (hy : y ∈ I ^ 2) :
    W.a₆ - y ^ 2 - W.a₃ * y ∈ I ^ 5 := by
  have h1x : W.a₁ * x ∈ I ^ 3 := by
    simpa only [pow_succ'] using Ideal.mul_mem_mul h1 hx
  have ht : W.a₁ * x * y ∈ I ^ 5 := by
    simpa only [← pow_add] using Ideal.mul_mem_mul h1x hy
  have hx2 : x ^ 2 ∈ I ^ 4 := by simpa only [← pow_mul] using Ideal.pow_mem_pow hx 2
  have hx3 : x ^ 3 ∈ I ^ 6 := by simpa only [← pow_mul] using Ideal.pow_mem_pow hx 3
  have h2x : W.a₂ * x ^ 2 ∈ I ^ 6 := by
    simpa only [← pow_add] using Ideal.mul_mem_mul h2 hx2
  have h4x : W.a₄ * x ∈ I ^ 5 := by
    simpa only [← pow_add] using Ideal.mul_mem_mul h4 hx
  have heq : W.a₆ - y ^ 2 - W.a₃ * y =
      W.a₁ * x * y - x ^ 3 - W.a₂ * x ^ 2 - W.a₄ * x := by
    linear_combination -(Affine.equation_iff _ _).mp he
  rw [heq]
  exact (I ^ 5).sub_mem ((I ^ 5).sub_mem ((I ^ 5).sub_mem ht
    (Ideal.pow_le_pow_right (by decide : 5 ≤ 6) hx3))
    (Ideal.pow_le_pow_right (by decide : 5 ≤ 6) h2x)) h4x

/-- Failure of the IV* b₆ test constructs the next integral normal form. -/
theorem exists_star_deep_y_translation {K : Type*} [Field K]
    (A : ValuationSubring K) (W : WeierstrassCurve A) {π : A} (hπ : π ≠ 0)
    (hgen : maximalIdeal A = Ideal.span {π})
    (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ ∈ maximalIdeal A ^ 2)
    (h3 : W.a₃ ∈ maximalIdeal A ^ 2) (h4 : W.a₄ ∈ maximalIdeal A ^ 3)
    (h6 : W.a₆ ∈ maximalIdeal A ^ 4) (hb6 : W.b₆ ∈ maximalIdeal A ^ 5)
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : ¬ SmoothReduction A W P) :
    ∃ t : A, t ∈ maximalIdeal A ^ 2 ∧
      let V := (VariableChange.mk 1 0 0 t : VariableChange A) • W
      V.a₁ ∈ maximalIdeal A ∧ V.a₂ ∈ maximalIdeal A ^ 2 ∧
      V.a₃ ∈ maximalIdeal A ^ 3 ∧ V.a₄ ∈ maximalIdeal A ^ 3 ∧
      V.a₆ ∈ maximalIdeal A ^ 5 := by
  obtain ⟨v⟩ := exists_typeIVStarCoordinates A W hπ hgen h1 h2 h3 h4 h6 P hP
  let y := π ^ 2 * v.y
  have hm (a : A) : π ^ 2 * a ∈ maximalIdeal A ^ 2 :=
    (maximalIdeal A ^ 2).mul_mem_right _
      (Ideal.pow_mem_pow (hgen ▸ Ideal.mem_span_singleton_self π) 2)
  have hc := star_translated_a6_mem_fifth W (maximalIdeal A) v.equation h1 h2 h4
    (hm v.x) (hm v.y)
  have h3' : W.a₃ + 2 * y ∈ maximalIdeal A ^ 3 := by
    apply (square_mem_fifth_iff_mem_cube hπ hgen).mp
    have heq : (W.a₃ + 2 * y) ^ 2 = W.b₆ - 4 * (W.a₆ - y ^ 2 - W.a₃ * y) := by
      rw [b₆]; ring
    rw [heq]
    exact (maximalIdeal A ^ 5).sub_mem hb6 ((maximalIdeal A ^ 5).mul_mem_left _ hc)
  have h4' : W.a₄ - y * W.a₁ ∈ maximalIdeal A ^ 3 :=
    (maximalIdeal A ^ 3).sub_mem h4 (by
      simpa only [pow_succ, y] using Ideal.mul_mem_mul (hm v.y) h1)
  rw [sub_right_comm] at hc
  refine ⟨y, hm v.y, ?_⟩
  dsimp
  simpa only [variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, Units.val_one, inv_one, one_pow, one_mul,
    zero_mul, mul_zero, zero_add, add_zero, sub_zero, zero_pow (by decide : 2 ≠ 0),
    zero_pow (by decide : 3 ≠ 0), mul_comm y W.a₃] using ⟨h1, h2, h3', h4', hc⟩

end FLT.Mazur
