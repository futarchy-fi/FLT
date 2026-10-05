/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula

/-!
# Integral polarization of the Weierstrass cubic

The mixed coefficient of the cubic on a line gives its third intersection
without division. This works over arbitrary commutative rings, including
nonreduced rings and residue characteristics two and three.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve MvPolynomial

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The coefficient of t in the cubic evaluated at P + t Q. -/
def cubicPolar (P Q : Fin 3 → R) : R :=
  P 1 ^ 2 * Q 2 + 2 * P 1 * Q 1 * P 2 +
    W.a₁ * (P 0 * P 1 * Q 2 + P 0 * Q 1 * P 2 + Q 0 * P 1 * P 2) +
    W.a₃ * (Q 1 * P 2 ^ 2 + 2 * P 1 * P 2 * Q 2) - 3 * P 0 ^ 2 * Q 0 -
    W.a₂ * (P 0 ^ 2 * Q 2 + 2 * P 0 * Q 0 * P 2) -
    W.a₄ * (Q 0 * P 2 ^ 2 + 2 * P 0 * P 2 * Q 2) - 3 * W.a₆ * P 2 ^ 2 * Q 2

/-- The homogeneous cubic restricted to a line, with its four coefficients explicit. -/
theorem cubicPolar_expansion (P Q : Fin 3 → R) (a b : R) :
    eval (a • P + b • Q) W.toProjective.polynomial =
      a ^ 3 * eval P W.toProjective.polynomial +
      a ^ 2 * b * cubicPolar W P Q + a * b ^ 2 * cubicPolar W Q P +
      b ^ 3 * eval Q W.toProjective.polynomial := by
  simp only [Projective.eval_polynomial, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    cubicPolar]
  ring

/-- A homogeneous representative of the third intersection with the line through P and Q. -/
def thirdIntersection (P Q : Fin 3 → R) : Fin 3 → R :=
  cubicPolar W P Q • Q - cubicPolar W Q P • P

/-- The third-intersection representative satisfies the cubic even when it is zero. -/
theorem thirdIntersection_equation {P Q : Fin 3 → R}
    (hP : W.toProjective.Equation P) (hQ : W.toProjective.Equation Q) :
    W.toProjective.Equation (thirdIntersection W P Q) := by
  change eval _ _ = 0 at hP hQ ⊢
  have he : thirdIntersection W P Q =
      (-cubicPolar W Q P) • P + cubicPolar W P Q • Q := by
    ext i
    simp only [thirdIntersection, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he, cubicPolar_expansion, hP, hQ]
  ring

/-- The X coordinate of the existing addition formula is the third-intersection X. -/
theorem thirdIntersection_x (P Q : Fin 3 → R) :
    thirdIntersection W P Q 0 = W.toProjective.addX P Q := by
  simp only [thirdIntersection, cubicPolar, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Projective.addX]
  ring

/-- The Y coordinate before elliptic negation is the third-intersection Y. -/
theorem thirdIntersection_y (P Q : Fin 3 → R) :
    thirdIntersection W P Q 1 = W.toProjective.negAddY P Q := by
  simp only [thirdIntersection, cubicPolar, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Projective.negAddY]
  ring

/-- The Z coordinate of the existing addition formula is the third-intersection Z. -/
theorem thirdIntersection_z (P Q : Fin 3 → R) :
    thirdIntersection W P Q 2 = W.toProjective.addZ P Q := by
  simp only [thirdIntersection, cubicPolar, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Projective.addZ]
  ring

/-- Elliptic negation preserves the homogeneous cubic over any commutative ring. -/
theorem projective_equation_negate {P : Fin 3 → R} (hP : W.toProjective.Equation P) :
    W.toProjective.Equation ![P 0, W.toProjective.negY P, P 2] := by
  rw [Projective.equation_iff] at hP ⊢
  simp only [Projective.fin3_def_ext, Projective.negY]
  linear_combination hP

/-- The projective addition polynomials satisfy the cubic integrally, without cancellation. -/
theorem projectiveAdd_equation {P Q : Fin 3 → R}
    (hP : W.toProjective.Equation P) (hQ : W.toProjective.Equation Q) :
    W.toProjective.Equation (W.toProjective.addXYZ P Q) := by
  have h := projective_equation_negate W (thirdIntersection_equation W hP hQ)
  simpa only [Projective.negY, thirdIntersection_x, thirdIntersection_y,
    thirdIntersection_z, Projective.addXYZ, Projective.addY, Projective.fin3_def_ext] using h

end FLT.Mazur.WeierstrassIntegralChart
