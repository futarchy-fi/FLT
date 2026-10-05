/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodePointDepth
public import Mathlib.Data.Nat.Find

/-!
# Extracting the common factor of nodal coordinates

For a principal maximal ideal, bounded ideal-adic depth produces primitive
scaled coordinates. The bound comes from the actual Weierstrass equation
and the exact depth of a₆, rather than from an assumed classification.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- Membership in a power of a principal maximal ideal gives an explicit common factor. -/
theorem exists_node_coordinate_factor {π x : R}
    (hgen : maximalIdeal R = Ideal.span {π}) (k : ℕ)
    (hx : x ∈ maximalIdeal R ^ k) : ∃ a : R, x = π ^ k * a := by
  rw [hgen, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  exact hx

/-- One extra ideal-adic depth makes the quotient by πᵏ lie in the maximal ideal. -/
theorem exists_node_deep_factor {π x : R}
    (hgen : maximalIdeal R = Ideal.span {π}) (k : ℕ)
    (hx : x ∈ maximalIdeal R ^ (k + 1)) :
    ∃ a : R, a ∈ maximalIdeal R ∧ x = π ^ k * a := by
  obtain ⟨b, hb⟩ := exists_node_coordinate_factor hgen (k + 1) hx
  have hπ : π ∈ maximalIdeal R := hgen ▸ Ideal.mem_span_singleton_self π
  refine ⟨π * b, (maximalIdeal R).mul_mem_right _ hπ, ?_⟩
  rw [hb, pow_succ, mul_assoc]

/-- A bounded pair of coordinates has a maximal common power and a primitive quotient pair. -/
theorem exists_node_primitive_coordinates {π x y : R}
    (hgen : maximalIdeal R = Ideal.span {π}) (N : ℕ)
    (hbound : ¬ (x ∈ maximalIdeal R ^ (N + 1) ∧ y ∈ maximalIdeal R ^ (N + 1))) :
    ∃ k : ℕ, k ≤ N ∧ ∃ a b : R,
      x = π ^ k * a ∧ y = π ^ k * b ∧ (IsUnit a ∨ IsUnit b) := by
  classical
  let P : ℕ → Prop := fun k => x ∈ maximalIdeal R ^ k ∧ y ∈ maximalIdeal R ^ k
  let k := Nat.findGreatest P N
  have h0 : P 0 := by simp [P]
  have hk : k ≤ N := Nat.findGreatest_le N
  have hmem : P k := Nat.findGreatest_spec (Nat.zero_le N) h0
  have hnext : ¬ P (k + 1) := by
    by_cases hlt : k < N
    · exact Nat.findGreatest_is_greatest (n := N) (k := k + 1) (by omega) (by omega)
    · have heq : k = N := by omega
      simpa only [heq, P] using hbound
  obtain ⟨a, ha⟩ := exists_node_coordinate_factor hgen k hmem.1
  obtain ⟨b, hb⟩ := exists_node_coordinate_factor hgen k hmem.2
  refine ⟨k, hk, a, b, ha, hb, ?_⟩
  by_contra h
  push Not at h
  have ha' : a ∈ maximalIdeal R := h.1
  have hb' : b ∈ maximalIdeal R := h.2
  have hπ : π ∈ maximalIdeal R := hgen ▸ Ideal.mem_span_singleton_self π
  have hp : π ^ k ∈ maximalIdeal R ^ k := Ideal.pow_mem_pow hπ k
  apply hnext
  constructor
  · rw [ha, pow_succ]
    exact Ideal.mul_mem_mul hp ha'
  · rw [hb, pow_succ]
    exact Ideal.mul_mem_mul hp hb'

/-- Every integral point on a deep nodal model has primitive coordinates at depth at most n/2. -/
theorem exists_node_point_coordinates (W : WeierstrassCurve R) {π x y : R}
    (hgen : maximalIdeal R = Ideal.span {π}) (he : W.toAffine.Equation x y)
    (n : ℕ) (h3 : W.a₃ ∈ maximalIdeal R ^ (n + 1))
    (h4 : W.a₄ ∈ maximalIdeal R ^ (n + 1)) (h6 : W.a₆ ∉ maximalIdeal R ^ (n + 1)) :
    ∃ k : ℕ, k ≤ n / 2 ∧ ∃ a b : R,
      x = π ^ k * a ∧ y = π ^ k * b ∧ (IsUnit a ∨ IsUnit b) :=
  exists_node_primitive_coordinates hgen (n / 2)
    (node_not_both_coordinates_deep W (maximalIdeal R) he n h3 h4 h6)

end FLT.Mazur
