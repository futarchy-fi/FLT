/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeightedPoleMonomials
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Normalizing a weighted cubic relation

Scaling both coordinates by the x³ coefficient turns a weighted cubic
relation into a Weierstrass equation. No extraction of square or cube roots
is involved, so the construction works in every characteristic.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeightedPoleMonomials
variable {k R : Type*} [CommRing k] [CommRing R]

/-- The first six monomials are exactly 1,x,y,x²,xy,x³. -/
theorem sum_six [Module k R] (c : Fin 6 → k) (x y : R) :
    ∑ j : Fin 6, c j • monomial x y j =
      c 0 • 1 + c 1 • x + c 2 • y + c 3 • x ^ 2 + c 4 • (x * y) + c 5 • x ^ 3 := by
  simp [Fin.sum_univ_succ, monomial, xExponent, yExponent, add_assoc]

/-- The normalized Weierstrass coefficients of the weighted relation. -/
def cubicCurve (c : Fin 6 → k) : WeierstrassCurve k where
  a₁ := -c 4
  a₂ := c 3
  a₃ := -(c 2 * c 5)
  a₄ := c 1 * c 5
  a₆ := c 0 * c 5 ^ 2

/-- Simultaneous scaling normalizes both leading terms of the cubic equation. -/
theorem cubicCurve_equation (φ : k →+* R) (c : Fin 6 → k) (x y : R)
    (he : y ^ 2 = φ (c 0) + φ (c 1) * x + φ (c 2) * y +
      φ (c 3) * x ^ 2 + φ (c 4) * (x * y) + φ (c 5) * x ^ 3) :
    ((cubicCurve c).map φ).toAffine.Equation (φ (c 5) * x) (φ (c 5) * y) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [cubicCurve, WeierstrassCurve.map, map_neg, map_mul, map_pow]
  linear_combination φ (c 5) ^ 2 * he

/-- Nonzero scaling over a field preserves all the original coordinate information. -/
theorem scaled_coordinates_injective {F : Type*} [Field F] (φ : F →+* R)
    (c : F) (hc : c ≠ 0) : Function.Injective (fun z : R ↦ φ c * z) := by
  intro x y he
  have hh := congrArg (fun z ↦ φ c⁻¹ * z) he
  simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul] using hh

end FLT.Mazur.WeightedPoleMonomials
