/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Tangent branches of scaled nodal points

Divide the equation of a point with common coordinate factor πᵏ by π²ᵏ.
When the divided a₃,a₄,a₆ still vanish modulo the maximal ideal, primitive
scaled coordinates lie on exactly one of the two distinct nodal tangents.
This is the branch calculation below half the discriminant depth, before
the group-addition and middle-depth cases.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R)

/-- Cancel the common coordinate factor in the actual Weierstrass equation. -/
theorem node_scaled_equation {π : R} (hπ : π ≠ 0) (k : ℕ) (x y b3 b4 b6 : R)
    (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
    (h6 : W.a₆ = π ^ (2 * k) * b6)
    (he : W.toAffine.Equation (π ^ k * x) (π ^ k * y)) :
    y ^ 2 + W.a₁ * x * y + b3 * y = π ^ k * x ^ 3 + W.a₂ * x ^ 2 + b4 * x + b6 := by
  apply mul_left_cancel₀ (pow_ne_zero (2 * k) hπ)
  have he' := (Affine.equation_iff _ _).mp he
  rw [h3, h4, h6] at he'
  simp only [two_mul, pow_add] at he' ⊢
  linear_combination he'

/-- The scaled equation reduces to the two tangent factors and the scaled constant term. -/
theorem node_scaled_tangent_equation [IsLocalRing R] {π : R} (hπ : π ≠ 0)
    (hπm : π ∈ maximalIdeal R) {k : ℕ} (hk : 1 ≤ k) (x y b3 b4 b6 : R)
    (h2 : W.a₂ ∈ maximalIdeal R) (hb3 : b3 ∈ maximalIdeal R)
    (hb4 : b4 ∈ maximalIdeal R)
    (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
    (h6 : W.a₆ = π ^ (2 * k) * b6)
    (he : W.toAffine.Equation (π ^ k * x) (π ^ k * y)) :
    residue R y * (residue R y + residue R W.a₁ * residue R x) = residue R b6 := by
  have h := congrArg (residue R) (node_scaled_equation W hπ k x y b3 b4 b6 h3 h4 h6 he)
  have hπ' := (residue_eq_zero_iff _).mpr hπm
  have h2' := (residue_eq_zero_iff _).mpr h2
  have h3' := (residue_eq_zero_iff _).mpr hb3
  have h4' := (residue_eq_zero_iff _).mpr hb4
  simp only [map_add, map_mul, map_pow, hπ', h2', h3', h4',
    zero_pow (by omega : k ≠ 0), zero_mul, add_zero, zero_add] at h
  linear_combination h

/-- Below the middle depth the scaled point lies on a nodal tangent. -/
theorem node_scaled_tangent_product [IsLocalRing R] {π : R} (hπ : π ≠ 0)
    (hπm : π ∈ maximalIdeal R) {k : ℕ} (hk : 1 ≤ k) (x y b3 b4 b6 : R)
    (h2 : W.a₂ ∈ maximalIdeal R) (hb3 : b3 ∈ maximalIdeal R)
    (hb4 : b4 ∈ maximalIdeal R) (hb6 : b6 ∈ maximalIdeal R)
    (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
    (h6 : W.a₆ = π ^ (2 * k) * b6)
    (he : W.toAffine.Equation (π ^ k * x) (π ^ k * y)) :
    residue R y * (residue R y + residue R W.a₁ * residue R x) = 0 := by
  rw [node_scaled_tangent_equation W hπ hπm hk x y b3 b4 b6 h2 hb3 hb4 h3 h4 h6 he]
  exact (residue_eq_zero_iff _).mpr hb6

/-- At the middle depth, a unit scaled constant term forces both tangent factors to be units. -/
theorem node_scaled_middle_units [IsLocalRing R] {π : R} (hπ : π ≠ 0)
    (hπm : π ∈ maximalIdeal R) {k : ℕ} (hk : 1 ≤ k) (x y b3 b4 b6 : R)
    (h2 : W.a₂ ∈ maximalIdeal R) (hb3 : b3 ∈ maximalIdeal R)
    (hb4 : b4 ∈ maximalIdeal R) (hb6 : IsUnit b6)
    (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
    (h6 : W.a₆ = π ^ (2 * k) * b6)
    (he : W.toAffine.Equation (π ^ k * x) (π ^ k * y)) :
    IsUnit y ∧ IsUnit (y + W.a₁ * x) := by
  have h := node_scaled_tangent_equation W hπ hπm hk x y b3 b4 b6 h2 hb3 hb4 h3 h4 h6 he
  have hn : residue R y * (residue R y + residue R W.a₁ * residue R x) ≠ 0 := by
    rw [h]
    exact (residue_ne_zero_iff_isUnit _).mpr hb6
  obtain ⟨hy, hz⟩ := mul_ne_zero_iff.mp hn
  exact ⟨(residue_ne_zero_iff_isUnit _).mp hy,
    (residue_ne_zero_iff_isUnit _).mp (by simpa only [map_add, map_mul] using hz)⟩

omit [IsDomain R] in
/-- Primitive coordinates on a split nodal tangent have unit x and exactly one vanishing branch. -/
theorem node_primitive_tangent_branches [IsLocalRing R] {x y : R}
    (h1 : IsUnit W.a₁) (hprim : IsUnit x ∨ IsUnit y)
    (he : residue R y * (residue R y + residue R W.a₁ * residue R x) = 0) :
    IsUnit x ∧
      ((y ∈ maximalIdeal R ∧ IsUnit (y + W.a₁ * x)) ∨
        (IsUnit y ∧ y + W.a₁ * x ∈ maximalIdeal R)) := by
  have h1' := (residue_ne_zero_iff_isUnit _).mpr h1
  have hx : residue R x ≠ 0 := by
    intro hx
    have hy : residue R y = 0 := by
      simpa only [hx, mul_zero, add_zero, mul_self_eq_zero] using he
    rcases hprim with h | h
    · exact (residue_ne_zero_iff_isUnit _).mpr h hx
    · exact (residue_ne_zero_iff_isUnit _).mpr h hy
  refine ⟨(residue_ne_zero_iff_isUnit _).mp hx, ?_⟩
  rcases mul_eq_zero.mp he with hy | hz
  · left
    refine ⟨(residue_eq_zero_iff _).mp hy, (residue_ne_zero_iff_isUnit _).mp ?_⟩
    simpa [hy] using mul_ne_zero h1' hx
  · right
    refine ⟨(residue_ne_zero_iff_isUnit _).mp ?_, (residue_eq_zero_iff _).mp ?_⟩
    · intro hy
      exact mul_ne_zero h1' hx (by simpa only [hy, zero_add] using hz)
    · simpa only [map_add, map_mul] using hz

end FLT.Mazur
