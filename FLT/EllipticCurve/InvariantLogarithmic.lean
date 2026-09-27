/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.InvariantDifferential
/-!
# Mixed logarithmic derivative identities

The difference of two affine `X`-coordinates is the quotient appearing in the
elliptic divisibility sequence addition law. Its second logarithmic derivative
is determined by the coordinates of the sum and difference of the points.
-/

@[expose] public section

namespace WeierstrassCurve.Affine
variable {K : Type*} [Field K] (E : Affine K) [DecidableEq K]

/-- The squared mixed velocity is controlled by the sum and difference coordinates. -/
lemma mixed_square {x₁ y₁ x₂ y₂ m n : K}
    (h₁ : E.Equation x₁ y₁) (h₂ : E.Equation x₂ y₂) (hx : x₁ ≠ x₂) :
    let xp := E.addX x₁ x₂ (E.slope x₁ x₂ y₁ y₂)
    let xm := E.addX x₁ x₂ (E.slope x₁ x₂ y₁ (E.negY x₂ y₂))
    (m * (2 * y₁ + E.a₁ * x₁ + E.a₃) - n * (2 * y₂ + E.a₁ * x₂ + E.a₃)) ^ 2 - 
      (x₁ - x₂) * (m ^ 2 * (6 * x₁ ^ 2 + E.b₂ * x₁ + E.b₄) -
        n ^ 2 * (6 * x₂ ^ 2 + E.b₂ * x₂ + E.b₄)) =
      ((m + n) ^ 2 * xp + (m - n) ^ 2 * xm - 2 * m ^ 2 * x₁ - 2 * n ^ 2 * x₂) * (x₁ - x₂) ^ 2 := by
  dsimp only
  simp only [slope_of_X_ne hx, addX, negY, b₂, b₄]
  rw [equation_iff] at h₁ h₂
  field_simp
  linear_combination (2 * m ^ 2 - 2 * n ^ 2) * (h₁ - h₂)
end WeierstrassCurve.Affine
namespace Derivation
variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] (D : Derivation R K K)

/-- The second logarithmic derivative of a field element. -/
noncomputable def logSecond (f : K) : K := D (D f / f)

/-- Second logarithmic derivatives turn nonzero products into sums. -/
lemma logSecond_mul {f g : K} (hf : f ≠ 0) (hg : g ≠ 0) :
    D.logSecond (f * g) = D.logSecond f + D.logSecond g := by
  have h : D (f * g)/(f * g) = D f/f + D g/g := by
    rw [D.leibniz, smul_eq_mul, smul_eq_mul]
    field_simp
    ring
  simp only [logSecond, h, map_add]

/-- Second logarithmic derivatives turn nonzero quotients into differences. -/
lemma logSecond_div {f g : K} (hf : f ≠ 0) (hg : g ≠ 0) :
    D.logSecond (f/g) = D.logSecond f - D.logSecond g := by
  have h : D (f/g)/(f/g) = D f/f - D g/g := by
    rw [D.leibniz_div]
    simp only [smul_eq_mul]
    field_simp
  simp only [logSecond, h, map_sub]

/-- Squaring doubles the second logarithmic derivative. -/
lemma logSecond_sq {f : K} (hf : f ≠ 0) : D.logSecond (f ^ 2) = 2 * D.logSecond f := by
  rw [pow_two, D.logSecond_mul hf hf, two_mul]
/-- The quotient-rule expression for the second logarithmic derivative. -/
lemma logSecond_eq (f : K) :
    D.logSecond f = (f * D (D f) - D f ^ 2) / f ^ 2 := by
  rw [logSecond, D.leibniz_div]
  simp only [smul_eq_mul, div_eq_mul_inv, inv_pow]
  ring

/-- Negation does not change the second logarithmic derivative. -/
lemma logSecond_neg (f : K) : D.logSecond (-f) = D.logSecond f := by
  simp [logSecond]

end Derivation
namespace WeierstrassCurve.Affine
variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (E : Affine K) [DecidableEq K] (D : Derivation R K K)

/-- The second logarithmic derivative of a coordinate difference, for points
with constant invariant speeds. -/
lemma logSecond_sub {x₁ y₁ x₂ y₂ m n : K}
    (h₁ : E.Equation x₁ y₁) (h₂ : E.Equation x₂ y₂) (hx : x₁ ≠ x₂)
    (ha₁ : D E.a₁ = 0) (ha₃ : D E.a₃ = 0) (hm : D m = 0) (hn : D n = 0)
    (dx₁ : D x₁ = m * (2 * y₁ + E.a₁ * x₁ + E.a₃))
    (dy₁ : D y₁ = m * (3 * x₁ ^ 2 + 2 * E.a₂ * x₁ + E.a₄ - E.a₁ * y₁))
    (dx₂ : D x₂ = n * (2 * y₂ + E.a₁ * x₂ + E.a₃))
    (dy₂ : D y₂ = n * (3 * x₂ ^ 2 + 2 * E.a₂ * x₂ + E.a₄ - E.a₁ * y₂)) :
    let xp := E.addX x₁ x₂ (E.slope x₁ x₂ y₁ y₂)
    let xm := E.addX x₁ x₂ (E.slope x₁ x₂ y₁ (E.negY x₂ y₂))
    D.logSecond (x₁ - x₂) =
      -((m + n) ^ 2 * xp + (m - n) ^ 2 * xm - 2 * m ^ 2 * x₁ - 2 * n ^ 2 * x₂) := by
  have h := E.mixed_square (m := m) (n := n) h₁ h₂ hx
  dsimp only at h ⊢
  simp only [Derivation.logSecond, map_sub, dx₁, dx₂, D.leibniz_div,
    D.leibniz, map_add, hm, hn, ha₁, ha₃, dy₁, dy₂,
    show D (2 : K) = 0 from D.map_natCast 2, smul_eq_mul]
  field_simp
  simp only [b₂, b₄] at h
  linear_combination - h
end WeierstrassCurve.Affine
