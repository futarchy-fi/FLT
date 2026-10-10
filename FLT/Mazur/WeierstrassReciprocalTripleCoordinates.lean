/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalCentering
public import FLT.Mazur.WeierstrassReciprocalTripleCentered

/-!
# Actual reciprocal homogeneous triple coordinates

Translate the centered calculation back to the original Weierstrass coordinates.
The comparison applies without any hypothesis that an output z-coordinate is a unit.
-/

@[expose] public section

namespace FLT.Mazur.WeierstrassIntegralAddition

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Homogeneous reciprocal triple outputs compare by the explicit cubic scale. -/
theorem reciprocal_triple_coordinates {x₁ x₂ x₃ y₁ y₂ y₃ l m r s : R}
    (hl : l * (x₁ - x₂) = y₁ - y₂)
    (hm : m * (x₂ - x₃) = y₂ - y₃)
    (hn : r * (W.toAffine.addY x₁ x₂ y₁ l - y₃) = W.toAffine.addX x₁ x₂ l - x₃)
    (ht : (l - m) * (1 + (l + W.a₁) * r) = (x₁ - x₃) * r)
    (hs : s - r + (l - m) * r * s = 0) (i : Fin 3) :
    reciprocalXYZ W (W.toAffine.addX x₁ x₂ l) x₃
        (W.toAffine.addY x₁ x₂ y₁ l) r i =
      (1 + (l - m) * r) ^ 3 *
        reciprocalXYZ W x₁ (W.toAffine.addX x₂ x₃ m) y₁ s i := by
  let a := W.a₂ + 3 * x₂
  let b := W.a₁
  let c := W.a₃ + W.a₁ * x₂ + 2 * y₂
  let x := x₁ - x₂
  let z := x₃ - x₂
  let u := W.toAffine.addX x₁ x₂ l - x₂
  let v := W.toAffine.addX x₂ x₃ m - x₂
  let q := 1 + b * r - (a + u + z) * r ^ 2
  let p := 1 + b * s - (a + x + v) * s ^ 2
  let t := 1 + (l - m) * r
  have hu : u = l ^ 2 + b * l - a - x := by
    dsimp [u, b, a, x, Affine.addX]
    ring
  have hv : v = m ^ 2 + b * m - a - z := by
    dsimp [v, b, a, z, Affine.addX]
    ring
  have hn' : r * (-(l + b) * u - c - m * z) = u - z := by
    rw [reciprocal_left_denominator_centered W hl hm] at hn
    convert hn using 1
    dsimp [u, z]
    ring
  have ht' : (l - m) * (1 + (l + b) * r) = (x - z) * r := by
    convert ht using 1
    dsimp [x, z]
    ring
  have hc := reciprocal_triple_centered_coordinates hu hv hn' ht' hs
  change r * q = t ^ 3 * (s * p) ∧ _ ∧ _ at hc
  have hxL : reciprocalXYZ W (W.toAffine.addX x₁ x₂ l) x₃
        (W.toAffine.addY x₁ x₂ y₁ l) r 0 - x₂ * r ^ 3 = r * q := by
    rw [reciprocalXYZ_centered_x]
    dsimp [q, a, b, u, z]
    ring
  have hxR : reciprocalXYZ W x₁ (W.toAffine.addX x₂ x₃ m) y₁ s 0 -
      x₂ * s ^ 3 = s * p := by
    rw [reciprocalXYZ_centered_x]
    dsimp [p, a, b, x, v]
    ring
  have hyL : reciprocalXYZ W (W.toAffine.addX x₁ x₂ l) x₃
        (W.toAffine.addY x₁ x₂ y₁ l) r 1 - y₂ * r ^ 3 =
      -(1 + b * r) * q + (1 + (l + b) * r) * u * r ^ 2 := by
    rw [reciprocalXYZ_centered_y, reciprocal_left_ordinate_constant W hl]
    dsimp [q, a, b, u, z]
    ring
  have hconst : y₁ + y₂ + W.a₃ + W.a₁ * x₂ = c + l * x := by
    dsimp [c, x]
    linear_combination -hl
  have hyR : reciprocalXYZ W x₁ (W.toAffine.addX x₂ x₃ m) y₁ s 1 -
      y₂ * s ^ 3 = -(1 + b * s) * p + x * s ^ 2 - (c + l * x) * s ^ 3 := by
    rw [reciprocalXYZ_centered_y, hconst]
    dsimp [p, a, b, x, v]
    ring
  rcases hc with ⟨hcX, hcY, hcZ⟩
  fin_cases i
  · change reciprocalXYZ W (W.toAffine.addX x₁ x₂ l) x₃
        (W.toAffine.addY x₁ x₂ y₁ l) r 0 =
      t ^ 3 * reciprocalXYZ W x₁ (W.toAffine.addX x₂ x₃ m) y₁ s 0
    linear_combination hxL - t ^ 3 * hxR + hcX + x₂ * hcZ
  · change reciprocalXYZ W (W.toAffine.addX x₁ x₂ l) x₃
        (W.toAffine.addY x₁ x₂ y₁ l) r 1 =
      t ^ 3 * reciprocalXYZ W x₁ (W.toAffine.addX x₂ x₃ m) y₁ s 1
    linear_combination hyL - t ^ 3 * hyR + hcY + y₂ * hcZ
  · exact hcZ

end FLT.Mazur.WeierstrassIntegralAddition
