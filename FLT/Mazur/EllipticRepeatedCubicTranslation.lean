/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticRepeatedCubicPoint
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# Translating an actual repeated-cubic point to the origin

Translation by (πx,π²y) preserves the early coefficient depths, kills a₆,
and puts a₄ in m³ when the divided x-label is repeated. The residual value
of e₂ + 3x distinguishes the double-root and triple-root branches.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

/-- The coefficients after translating an actual point in the I₀* chart. -/
theorem starZero_point_translation_coefficients {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (π x y e1 e2 e3 e4 : R)
    (h1 : W.a₁ = π * e1) (h2 : W.a₂ = π * e2)
    (h3 : W.a₃ = π ^ 2 * e3) (h4 : W.a₄ = π ^ 2 * e4)
    (he : W.toAffine.Equation (π * x) (π ^ 2 * y)) :
    let V := (VariableChange.mk 1 (π * x) 0 (π ^ 2 * y) : VariableChange R) • W
    V.a₁ = π * e1 ∧ V.a₂ = π * (e2 + 3 * x) ∧
    V.a₃ = π ^ 2 * (e3 + x * e1 + 2 * y) ∧
    V.a₄ = π ^ 2 * (e4 + 2 * x * e2 + 3 * x ^ 2 - π * y * e1) ∧ V.a₆ = 0 := by
  have he' := (Affine.equation_iff _ _).mp he
  dsimp
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, Units.val_one, inv_one, one_pow, one_mul,
    zero_mul, mul_zero, add_zero, sub_zero, zero_pow (by decide : 2 ≠ 0),
    h1, h2, h3, h4]
  refine ⟨True.intro, by ring, by ring, by ring, ?_⟩
  rw [h1, h2, h3, h4] at he'
  linear_combination -he'

/-- A repeated divided x-label deepens a₄ after translation by the actual point. -/
theorem repeatedCubic_point_translation_depths {R : Type*} [CommRing R] [IsLocalRing R]
    (W : WeierstrassCurve R) {π : R} (hπm : π ∈ maximalIdeal R)
    (x y e1 e2 e3 e4 : R) (h1 : W.a₁ = π * e1) (h2 : W.a₂ = π * e2)
    (h3 : W.a₃ = π ^ 2 * e3) (h4 : W.a₄ = π ^ 2 * e4)
    (he : W.toAffine.Equation (π * x) (π ^ 2 * y))
    (hd : 3 * residue R x ^ 2 + 2 * residue R e2 * residue R x + residue R e4 = 0) :
    let V := (VariableChange.mk 1 (π * x) 0 (π ^ 2 * y) : VariableChange R) • W
    V.a₁ ∈ maximalIdeal R ∧ V.a₂ = π * (e2 + 3 * x) ∧
    V.a₃ ∈ maximalIdeal R ^ 2 ∧ V.a₄ ∈ maximalIdeal R ^ 3 ∧ V.a₆ = 0 := by
  obtain ⟨ha, hb, hc, hd', he'⟩ := starZero_point_translation_coefficients W π x y
    e1 e2 e3 e4 h1 h2 h3 h4 he
  refine ⟨ha ▸ (maximalIdeal R).mul_mem_right _ hπm, hb,
    hc ▸ (maximalIdeal R ^ 2).mul_mem_right _ (Ideal.pow_mem_pow hπm 2), ?_, he'⟩
  rw [hd', pow_succ]
  apply Ideal.mul_mem_mul (Ideal.pow_mem_pow hπm 2)
  apply (residue_eq_zero_iff _).mp
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat,
    (residue_eq_zero_iff _).mpr hπm, zero_mul, sub_zero]
  linear_combination hd

/-- The triple-root test is exactly the depth-two test for the translated a₂. -/
theorem repeatedCubic_translated_a2_mem_square_iff {R : Type*} [CommRing R]
    [IsDomain R] [IsLocalRing R] {π e2 x : R} (hπ : π ≠ 0)
    (hgen : maximalIdeal R = Ideal.span {π}) :
    π * (e2 + 3 * x) ∈ maximalIdeal R ^ 2 ↔ residue R e2 + 3 * residue R x = 0 := by
  constructor
  · intro h
    have hm := node_factor_mem_maximalIdeal hπ hgen 1 (by simpa only [pow_one] using h)
    simpa only [map_add, map_mul, map_ofNat] using (residue_eq_zero_iff _).mpr hm
  · intro h
    have hm : e2 + 3 * x ∈ maximalIdeal R :=
      (residue_eq_zero_iff _).mp (by simpa only [map_add, map_mul, map_ofNat] using h)
    simpa only [pow_two] using
      Ideal.mul_mem_mul (hgen ▸ Ideal.mem_span_singleton_self π) hm

end FLT.Mazur
