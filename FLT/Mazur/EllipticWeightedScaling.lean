/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeCoordinateFactor
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# Integral weighted scaling of a Weierstrass equation

Coefficient depths (1,2,3,4,6) produce an integral equation by division by
the corresponding powers of π. The generic equations are related by the
actual variable change (π,0,0,0), and their discriminants differ by π¹².
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

/-- Weighted coefficient scaling multiplies the discriminant by the twelfth power. -/
theorem discriminant_of_weighted_coefficients {R : Type*} [CommRing R]
    (W U : WeierstrassCurve R) (π : R)
    (h1 : W.a₁ = π * U.a₁) (h2 : W.a₂ = π ^ 2 * U.a₂)
    (h3 : W.a₃ = π ^ 3 * U.a₃) (h4 : W.a₄ = π ^ 4 * U.a₄)
    (h6 : W.a₆ = π ^ 6 * U.a₆) : W.Δ = π ^ 12 * U.Δ := by
  simp only [Δ, b₂, b₄, b₆, b₈, h1, h2, h3, h4, h6]
  ring

/-- The weighted depth conditions construct an integral equation with smaller scaling. -/
theorem exists_integral_weighted_model {R : Type*} [CommRing R] [IsLocalRing R]
    (W : WeierstrassCurve R) {π : R} (hgen : maximalIdeal R = Ideal.span {π})
    (h1 : W.a₁ ∈ maximalIdeal R) (h2 : W.a₂ ∈ maximalIdeal R ^ 2)
    (h3 : W.a₃ ∈ maximalIdeal R ^ 3) (h4 : W.a₄ ∈ maximalIdeal R ^ 4)
    (h6 : W.a₆ ∈ maximalIdeal R ^ 6) :
    ∃ U : WeierstrassCurve R, W.a₁ = π * U.a₁ ∧ W.a₂ = π ^ 2 * U.a₂ ∧
      W.a₃ = π ^ 3 * U.a₃ ∧ W.a₄ = π ^ 4 * U.a₄ ∧ W.a₆ = π ^ 6 * U.a₆ ∧
      W.Δ = π ^ 12 * U.Δ := by
  obtain ⟨e1, he1⟩ := exists_node_coordinate_factor hgen 1 (by simpa using h1)
  obtain ⟨e2, he2⟩ := exists_node_coordinate_factor hgen 2 h2
  obtain ⟨e3, he3⟩ := exists_node_coordinate_factor hgen 3 h3
  obtain ⟨e4, he4⟩ := exists_node_coordinate_factor hgen 4 h4
  obtain ⟨e6, he6⟩ := exists_node_coordinate_factor hgen 6 h6
  simp only [pow_one] at he1
  let U : WeierstrassCurve R := ⟨e1, e2, e3, e4, e6⟩
  exact ⟨U, he1, he2, he3, he4, he6,
    discriminant_of_weighted_coefficients W U π he1 he2 he3 he4 he6⟩

/-- The divided integral equation is obtained by an actual generic variable change. -/
theorem weighted_model_variableChange {R K : Type*} [CommRing R] [Field K]
    (f : R →+* K) (W U : WeierstrassCurve R) {π : R} (hπ : f π ≠ 0)
    (h1 : W.a₁ = π * U.a₁) (h2 : W.a₂ = π ^ 2 * U.a₂)
    (h3 : W.a₃ = π ^ 3 * U.a₃) (h4 : W.a₄ = π ^ 4 * U.a₄)
    (h6 : W.a₆ = π ^ 6 * U.a₆) :
    (VariableChange.mk (Units.mk0 (f π) hπ) 0 0 0 : VariableChange K) • W.map f = U.map f := by
  ext <;> simp [variableChange_def, map, h1, h2, h3, h4, h6, hπ, ← mul_assoc]

end FLT.Mazur
