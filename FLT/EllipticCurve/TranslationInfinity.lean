/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.MultiplicationInfinity
/-!
# Translated coordinates at infinity

Writing the chord formulas using the differences x-u and y-v makes their
behavior at infinity explicit. The coefficients are the partial derivatives
of the Weierstrass equation at the translating point.
-/

@[expose] public section

open Polynomial
open scoped WeierstrassCurve.Affine
namespace WeierstrassCurve.Affine.FunctionField
variable {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
  (W : Affine F) [W.IsElliptic]
set_option backward.isDefEq.respectTransparency false in
/-- The difference between translated x and the translating abscissa,
with numerator expressed in the two coordinate differences. -/
theorem translationPullback_genericX_sub {u v : F} (h : W.Nonsingular u v) :
    let U := algebraMap F W.FunctionField u
    let V := algebraMap F W.FunctionField v
    let A := algebraMap F W.FunctionField (3 * u ^ 2 + 2 * W.a₂ * u + W.a₄ - W.a₁ * v)
    let B := algebraMap F W.FunctionField (2 * v + W.a₁ * u + W.a₃)
    translationPullback W (Point.some u v h) (genericX W) - U =
      (A * (genericX W - U) - B * (genericY W - V)) / (genericX W - U) ^ 2 := by
  dsimp only
  have hx : genericX W ≠ algebraMap F W.FunctionField u := by
    intro he
    exact genericX_transcendental W (he ▸ isAlgebraic_algebraMap u)
  have hgen := generic_equation W
  rw [equation_iff'] at hgen
  have hbase := congrArg (algebraMap F W.FunctionField) ((W.equation_iff' u v).mp h.1)
  rw [(translationPullback_coordinates W h).1, addX]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero] at hbase ⊢
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆] at hgen ⊢
  field_simp [sub_ne_zero.mpr hx]
  linear_combination hgen - hbase
set_option backward.isDefEq.respectTransparency false in
/-- The translated y-difference in terms of the translated x-difference
and the chord slope. -/
theorem translationPullback_genericY_sub {u v : F} (h : W.Nonsingular u v) :
    let U := algebraMap F W.FunctionField u
    let V := algebraMap F W.FunctionField v
    let B := algebraMap F W.FunctionField (2 * v + W.a₁ * u + W.a₃)
    translationPullback W (Point.some u v h) (genericY W) - V =
      -((genericY W - V) / (genericX W - U) + algebraMap F W.FunctionField W.a₁) *
        (translationPullback W (Point.some u v h) (genericX W) - U) - B := by
  dsimp only
  have hx : genericX W ≠ algebraMap F W.FunctionField u := by
    intro he
    exact genericX_transcendental W (he ▸ isAlgebraic_algebraMap u)
  rw [(translationPullback_coordinates W h).1, (translationPullback_coordinates W h).2,
    addY, negAddY, negY]
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₃, map_add, map_mul, map_ofNat]
  field_simp [sub_ne_zero.mpr hx]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The translated y-difference has a numerator with pole order at most five
and denominator (x-u)³, with pole order six. -/
theorem translationPullback_genericY_sub_formula {u v : F} (h : W.Nonsingular u v) :
    let U := algebraMap F W.FunctionField u
    let V := algebraMap F W.FunctionField v
    let A := algebraMap F W.FunctionField (3 * u ^ 2 + 2 * W.a₂ * u + W.a₄ - W.a₁ * v)
    let B := algebraMap F W.FunctionField (2 * v + W.a₁ * u + W.a₃)
    let dx := genericX W - U
    let dy := genericY W - V
    translationPullback W (Point.some u v h) (genericY W) - V =
      (-(B ^ 2 + A * dx) * dy +
        (B * (3 * U + algebraMap F W.FunctionField W.a₂) -
          algebraMap F W.FunctionField W.a₁ * A) * dx ^ 2 + B * A * dx) / dx ^ 3 := by
  dsimp only
  have hx : genericX W ≠ algebraMap F W.FunctionField u := by
    intro he
    exact genericX_transcendental W (he ▸ isAlgebraic_algebraMap u)
  rw [translationPullback_genericY_sub W h, translationPullback_genericX_sub W h]
  have hgen := generic_equation W
  rw [equation_iff'] at hgen
  have hbase := congrArg (algebraMap F W.FunctionField) ((W.equation_iff' u v).mp h.1)
  simp only [WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆, map_add, map_sub, map_mul, map_pow, map_ofNat,
    map_zero] at hgen hbase ⊢
  field_simp [sub_ne_zero.mpr hx]
  linear_combination (2 * algebraMap F W.FunctionField v +
    algebraMap F W.FunctionField W.a₁ * algebraMap F W.FunctionField u +
    algebraMap F W.FunctionField W.a₃) * (hgen - hbase)
end WeierstrassCurve.Affine.FunctionField

namespace WeierstrassCurve.Affine.FunctionField
open WithZero

variable {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
  (W : Affine F) [W.IsElliptic]
/-- Both translated coordinates approach the translating point at infinity:
their differences from its coordinates have order at least one. -/
theorem infinityValuation_translation_coordinates_sub_le {u v : F} (h : W.Nonsingular u v) :
    infinityValuation W (translationPullback W (Point.some u v h) (genericX W) -
      algebraMap F W.FunctionField u) ≤ exp (-1 : ℤ) ∧
    infinityValuation W (translationPullback W (Point.some u v h) (genericY W) -
      algebraMap F W.FunctionField v) ≤ exp (-1 : ℤ) := by
  let ν := infinityValuation W
  let dx := genericX W - algebraMap F W.FunctionField u
  let dy := genericY W - algebraMap F W.FunctionField v
  let a := 3 * u ^ 2 + 2 * W.a₂ * u + W.a₄ - W.a₁ * v
  let b := 2 * v + W.a₁ * u + W.a₃
  let c := b * (3 * u + W.a₂) - W.a₁ * a
  let A := algebraMap F W.FunctionField a
  let B := algebraMap F W.FunctionField b
  let C := algebraMap F W.FunctionField c
  have hconst (d : F) : ν (algebraMap F W.FunctionField d) ≤ exp (0 : ℤ) :=
    Valuation.IsTrivialOn.valuation_algebraMap_le_one ν d
  have hmul {f g : W.FunctionField} {i j : ℤ} (hf : ν f ≤ exp i) (hg : ν g ≤ exp j) :
      ν (f * g) ≤ exp (i + j) := by
    rw [map_mul, exp_add]
    gcongr
  have hadd {f g : W.FunctionField} {i : ℤ} (hf : ν f ≤ exp i) (hg : ν g ≤ exp i) :
      ν (f + g) ≤ exp i := (ν.map_add _ _).trans (max_le hf hg)
  have hsub {f g : W.FunctionField} {i : ℤ} (hf : ν f ≤ exp i) (hg : ν g ≤ exp i) :
      ν (f - g) ≤ exp i := (ν.map_sub _ _).trans (max_le hf hg)
  have hmono {i j : ℤ} (hij : i ≤ j) : exp i ≤ exp j := exp_le_exp.mpr hij
  have hx : ν dx = exp (2 : ℤ) := by
    simpa [dx] using infinityValuation_aeval_genericX W
      (p := X - Polynomial.C u) (X_sub_C_ne_zero u)
  have hx0 : ν (genericX W) = exp (2 : ℤ) := by
    simpa using infinityValuation_aeval_genericX W (p := X) X_ne_zero
  have hy0 : ν (genericY W) = exp (3 : ℤ) :=
    infinityValuation_y_of_equation W (generic_equation W) hx0
  have hy : ν dy = exp (3 : ℤ) := by
    exact (ν.map_sub_eq_of_lt_left ((hconst v).trans_lt
      (by rw [hy0]; exact exp_lt_exp.mpr (by norm_num)))).trans hy0
  have hA : ν A ≤ exp (0 : ℤ) := hconst a
  have hB : ν B ≤ exp (0 : ℤ) := hconst b
  have hC : ν C ≤ exp (0 : ℤ) := hconst c
  have hx2 : ν (dx ^ 2) = exp (4 : ℤ) := by rw [map_pow, hx, ← exp_nsmul]; rfl
  have hx3 : ν (dx ^ 3) = exp (6 : ℤ) := by rw [map_pow, hx, ← exp_nsmul]; rfl
  have hnx : ν (A * dx - B * dy) ≤ exp (3 : ℤ) :=
    hsub ((hmul hA hx.le).trans (hmono (by norm_num)))
      ((hmul hB hy.le).trans (hmono (by norm_num)))
  have hn1 : ν (-(B ^ 2 + A * dx) * dy) ≤ exp (5 : ℤ) := by
    apply (hmul (i := 2) (j := 3) ?_ hy.le)
    rw [ν.map_neg]
    apply hadd
    · have hBB : ν (B ^ 2) ≤ exp (0 : ℤ) := by
        simpa only [pow_two, zero_add] using hmul hB hB
      exact hBB.trans (hmono (by norm_num))
    · exact (hmul hA hx.le).trans (hmono (by norm_num))
  have hn2 : ν (C * dx ^ 2) ≤ exp (5 : ℤ) :=
    (hmul hC hx2.le).trans (hmono (by norm_num))
  have hn3 : ν (B * A * dx) ≤ exp (5 : ℤ) :=
    (hmul (hmul hB hA) hx.le).trans (hmono (by norm_num))
  constructor
  · rw [translationPullback_genericX_sub W h]
    change ν ((A * dx - B * dy) / dx ^ 2) ≤ exp (-1 : ℤ)
    rw [map_div₀, hx2, div_le_iff₀ (by exact exp_pos), ← exp_add]
    exact hnx
  · have he := translationPullback_genericY_sub_formula W h
    have he' : translationPullback W (Point.some u v h) (genericY W) -
        algebraMap F W.FunctionField v =
        (-(B ^ 2 + A * dx) * dy + C * dx ^ 2 + B * A * dx) / dx ^ 3 := by
      simpa only [A, B, C, a, b, c, dx, dy, map_sub, map_add, map_mul, map_ofNat] using he
    rw [he']
    change ν ((-(B ^ 2 + A * dx) * dy + C * dx ^ 2 + B * A * dx) / dx ^ 3) ≤ _
    rw [map_div₀, hx3, div_le_iff₀ (by exact exp_pos), ← exp_add]
    exact hadd (hadd hn1 hn2) hn3
end WeierstrassCurve.Affine.FunctionField
