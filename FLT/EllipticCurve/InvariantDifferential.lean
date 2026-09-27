/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.InvariantDerivation
/-!
# Invariant differentials and affine addition

The chord identity controls the derivative of the slope for two moving points.
The resulting formulas add their speeds along the invariant vector field.
The tangent formulas handle doubling separately and do not divide by two.
-/

@[expose] public section

open Polynomial
namespace WeierstrassCurve.Affine
variable {K : Type*} [Field K] (E : Affine K) [DecidableEq K]

/-- The tangent numerator at one endpoint of a chord factors through the other
endpoint and the sum of the points. -/
lemma chord_tangent {x₁ y₁ x₂ y₂ : K} (h₁ : E.Equation x₁ y₁) (h₂ : E.Equation x₂ y₂)
    (hx : x₁ ≠ x₂) :
    let l := E.slope x₁ x₂ y₁ y₂
    (3 * x₁ ^ 2 + 2 * E.a₂ * x₁ + E.a₄ - E.a₁ * y₁) - l * (2 * y₁ + E.a₁ * x₁ + E.a₃) =
      (x₁ - x₂) * (x₁ - E.addX x₁ x₂ l) := by
  dsimp
  rw [slope_of_X_ne hx]
  rw [equation_iff] at h₁ h₂
  field_simp
  linear_combination h₂ - h₁

variable {R : Type*} [CommRing R] [Algebra R K] (D : Derivation R K K)

/-- The derivative of the chord slope for points with invariant speeds `m` and `n`. -/
lemma deriv_slope {x₁ y₁ x₂ y₂ m n : K}
    (h₁ : E.Equation x₁ y₁) (h₂ : E.Equation x₂ y₂) (hx : x₁ ≠ x₂)
    (dx₁ : D x₁ = m * (2 * y₁ + E.a₁ * x₁ + E.a₃))
    (dy₁ : D y₁ = m * (3 * x₁ ^ 2 + 2 * E.a₂ * x₁ + E.a₄ - E.a₁ * y₁))
    (dx₂ : D x₂ = n * (2 * y₂ + E.a₁ * x₂ + E.a₃))
    (dy₂ : D y₂ = n * (3 * x₂ ^ 2 + 2 * E.a₂ * x₂ + E.a₄ - E.a₁ * y₂)) :
    D (E.slope x₁ x₂ y₁ y₂) =
      m * (x₁ - E.addX x₁ x₂ (E.slope x₁ x₂ y₁ y₂)) + 
      n * (x₂ - E.addX x₁ x₂ (E.slope x₁ x₂ y₁ y₂)) := by
  have ht₁ := E.chord_tangent h₁ h₂ hx
  have ht₂ := E.chord_tangent h₂ h₁ hx.symm
  dsimp only at ht₁ ht₂
  have hs : E.slope x₂ x₁ y₂ y₁ = E.slope x₁ x₂ y₁ y₂ := by
    rw [slope_of_X_ne hx, slope_of_X_ne hx.symm, ← neg_sub x₁ x₂,
      ← neg_sub y₁ y₂, neg_div_neg_eq]
  rw [hs, show E.addX x₂ x₁ (E.slope x₁ x₂ y₁ y₂) =
      E.addX x₁ x₂ (E.slope x₁ x₂ y₁ y₂) by simp only [addX]; ring] at ht₂
  simp only [slope_of_X_ne hx] at * 
  rw [D.leibniz_div]
  simp only [map_sub, dx₁, dy₁, dx₂, dy₂, smul_eq_mul]
  field_simp at * 
  linear_combination m * ht₁ - n * ht₂

/-- Addition adds the invariant speeds in the first affine coordinate. -/
lemma deriv_addX {x₁ y₁ x₂ y₂ m n : K}
    (h₁ : E.Equation x₁ y₁) (h₂ : E.Equation x₂ y₂) (hx : x₁ ≠ x₂)
    (ha₁ : D E.a₁ = 0) (ha₂ : D E.a₂ = 0)
    (dx₁ : D x₁ = m * (2 * y₁ + E.a₁ * x₁ + E.a₃))
    (dy₁ : D y₁ = m * (3 * x₁ ^ 2 + 2 * E.a₂ * x₁ + E.a₄ - E.a₁ * y₁))
    (dx₂ : D x₂ = n * (2 * y₂ + E.a₁ * x₂ + E.a₃))
    (dy₂ : D y₂ = n * (3 * x₂ ^ 2 + 2 * E.a₂ * x₂ + E.a₄ - E.a₁ * y₂)) :
    let l := E.slope x₁ x₂ y₁ y₂
    D (E.addX x₁ x₂ l) =
      (m + n) * (2 * E.addY x₁ x₂ y₁ l + E.a₁ * E.addX x₁ x₂ l + E.a₃) := by
  have hd := E.deriv_slope D h₁ h₂ hx dx₁ dy₁ dx₂ dy₂
  have hl : E.slope x₁ x₂ y₁ y₂ * (x₁ - x₂) = y₁ - y₂ := by
    rw [slope_of_X_ne hx, div_mul_cancel₀ _ (sub_ne_zero.mpr hx)]
  dsimp only
  simp only [addX, map_sub, map_add, D.leibniz_pow, D.leibniz, ha₁, ha₂,
    smul_eq_mul, dx₁, dx₂, hd,
    show 2 - 1=1 by decide, pow_one, nsmul_eq_mul, Nat.cast_ofNat,
    addY, negY, negAddY]
  simp only [addX] at hd
  linear_combination - 2 * n * hl

/-- Addition adds the invariant speeds in the second affine coordinate. -/
lemma deriv_addY {x₁ y₁ x₂ y₂ m n : K}
    (h₁ : E.Equation x₁ y₁) (h₂ : E.Equation x₂ y₂) (hx : x₁ ≠ x₂)
    (ha₁ : D E.a₁ = 0) (ha₂ : D E.a₂ = 0) (ha₃ : D E.a₃ = 0)
    (dx₁ : D x₁ = m * (2 * y₁ + E.a₁ * x₁ + E.a₃))
    (dy₁ : D y₁ = m * (3 * x₁ ^ 2 + 2 * E.a₂ * x₁ + E.a₄ - E.a₁ * y₁))
    (dx₂ : D x₂ = n * (2 * y₂ + E.a₁ * x₂ + E.a₃))
    (dy₂ : D y₂ = n * (3 * x₂ ^ 2 + 2 * E.a₂ * x₂ + E.a₄ - E.a₁ * y₂)) :
    let l := E.slope x₁ x₂ y₁ y₂
    D (E.addY x₁ x₂ y₁ l) =
      (m + n) * (3 * (E.addX x₁ x₂ l) ^ 2 + 2 * E.a₂ * (E.addX x₁ x₂ l) + E.a₄ - 
        E.a₁ * (E.addY x₁ x₂ y₁ l)) := by
  have hd := E.deriv_slope D h₁ h₂ hx dx₁ dy₁ dx₂ dy₂
  have hdX := E.deriv_addX D h₁ h₂ hx ha₁ ha₂ dx₁ dy₁ dx₂ dy₂
  have ht := E.chord_tangent h₁ h₂ hx
  dsimp only at hdX ht ⊢
  simp only [addY, negY, negAddY, map_neg, map_sub, map_add, D.leibniz,
    ha₁, ha₃, smul_eq_mul, dx₁, dy₁, hd, hdX]
  simp only [addX] at ht ⊢
  linear_combination - (2 * m + n) * ht

/-- The derivative of the tangent slope along the invariant vector field. -/
lemma deriv_tangentSlope {x y m : K} (hy : y ≠ E.negY x y)
    (ha₁ : D E.a₁ = 0) (ha₂ : D E.a₂ = 0) (ha₃ : D E.a₃ = 0) (ha₄ : D E.a₄ = 0)
    (dx : D x = m * (2 * y + E.a₁ * x + E.a₃))
    (dy : D y = m * (3 * x ^ 2 + 2 * E.a₂ * x + E.a₄ - E.a₁ * y)) :
    D (E.slope x x y y) = 2 * m * (x - E.addX x x (E.slope x x y y)) := by
  have hf : 2 * y + E.a₁ * x + E.a₃ ≠ 0 := by
    convert sub_ne_zero.mpr hy using 1
    simp only [negY]
    ring
  have hs : E.slope x x y y = (3 * x ^ 2 + 2 * E.a₂ * x + E.a₄ - E.a₁ * y) /
      (2 * y + E.a₁ * x + E.a₃) := by
    rw [slope_of_Y_ne rfl hy]
    congr 1
    simp only [negY]
    ring
  rw [hs]
  simp only [D.leibniz_div, D.leibniz, D.leibniz_pow, map_sub, map_add,
    (show D (2 : K) = 0 from D.map_natCast 2),
    (show D (3 : K) = 0 from D.map_natCast 3), ha₁, ha₂, ha₃, ha₄, dx, dy,
    smul_eq_mul, nsmul_eq_mul,
    Nat.cast_ofNat, show 2 - 1=1 by decide, pow_one, addX]
  field_simp [hf]
  ring

/-- Doubling doubles the invariant speed in the first affine coordinate. -/
lemma deriv_doubleX {x y m : K} (hy : y ≠ E.negY x y)
    (ha₁ : D E.a₁ = 0) (ha₂ : D E.a₂ = 0) (ha₃ : D E.a₃ = 0) (ha₄ : D E.a₄ = 0)
    (dx : D x = m * (2 * y + E.a₁ * x + E.a₃))
    (dy : D y = m * (3 * x ^ 2 + 2 * E.a₂ * x + E.a₄ - E.a₁ * y)) :
    let l := E.slope x x y y
    D (E.addX x x l) =
      (2 * m) * (2 * E.addY x x y l + E.a₁ * E.addX x x l + E.a₃) := by
  have hd := E.deriv_tangentSlope D hy ha₁ ha₂ ha₃ ha₄ dx dy
  dsimp only
  simp only [addX, map_sub, map_add, D.leibniz_pow, D.leibniz, ha₁, ha₂,
    smul_eq_mul, dx, hd,
    show 2 - 1=1 by decide, pow_one, nsmul_eq_mul, Nat.cast_ofNat,
    addY, negY, negAddY]
  simp only [addX] at hd
  ring

/-- Doubling doubles the invariant speed in the second affine coordinate. -/
lemma deriv_doubleY {x y m : K} (hy : y ≠ E.negY x y)
    (ha₁ : D E.a₁ = 0) (ha₂ : D E.a₂ = 0) (ha₃ : D E.a₃ = 0) (ha₄ : D E.a₄ = 0)
    (dx : D x = m * (2 * y + E.a₁ * x + E.a₃))
    (dy : D y = m * (3 * x ^ 2 + 2 * E.a₂ * x + E.a₄ - E.a₁ * y)) :
    let l := E.slope x x y y
    D (E.addY x x y l) =
      (2 * m) * (3 * (E.addX x x l) ^ 2 + 2 * E.a₂ * (E.addX x x l) + E.a₄ - 
        E.a₁ * (E.addY x x y l)) := by
  have hd := E.deriv_tangentSlope D hy ha₁ ha₂ ha₃ ha₄ dx dy
  have hdX := E.deriv_doubleX D hy ha₁ ha₂ ha₃ ha₄ dx dy
  have ht : (3 * x ^ 2 + 2 * E.a₂ * x + E.a₄ - E.a₁ * y) - 
      E.slope x x y y * (2 * y + E.a₁ * x + E.a₃) = 0 := by
    rw [slope_of_Y_ne rfl hy]
    have he : 2 * y + E.a₁ * x + E.a₃ = y - E.negY x y := by simp only [negY]; ring
    rw [he, div_mul_cancel₀ _ (sub_ne_zero.mpr hy), sub_self]
  dsimp only at hdX ⊢
  simp only [addY, negY, negAddY, map_neg, map_sub, map_add, D.leibniz,
    ha₁, ha₃, smul_eq_mul, dx, dy, hd, hdX]
  simp only [addX] at ht ⊢
  linear_combination - (3 * m) * ht
end WeierstrassCurve.Affine
