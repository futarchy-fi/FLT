/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityAdditionFormula

/-!
# Homogeneous differences of infinity line cubics

The divided Z-difference is quadratic in homogeneous coordinates. It compares
arbitrary secants, including outer secants with different intercepts, without
inverting either a slope difference or a leading coefficient.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The homogeneous divided Z-difference of the Weierstrass cubic. -/
def infinityCubicDividedZ (X Y Z Z' : R) : R :=
  Y ^ 2 + W.a₁ * X * Y + W.a₃ * (Z + Z') * Y - W.a₂ * X ^ 2 -
    W.a₄ * X * (Z + Z') - W.a₆ * (Z ^ 2 + Z * Z' + Z' ^ 2)

/-- Setting Y to one recovers the actual infinity slope denominator. -/
theorem infinityCubicDividedZ_one (X Z Z' : R) :
    infinityCubicDividedZ W X 1 Z Z' = infinitySlopeDenominator W X Z Z' := by
  simp only [infinityCubicDividedZ, infinitySlopeDenominator, one_pow, mul_one]

/-- The divided Z-difference is symmetric in its two Z arguments. -/
theorem infinityCubicDividedZ_swap (X Y Z Z' : R) :
    infinityCubicDividedZ W X Y Z Z' = infinityCubicDividedZ W X Y Z' Z := by
  unfold infinityCubicDividedZ
  ring

/-- Exact homogeneous cubic subtraction, over every commutative coefficient ring. -/
theorem infinityCubic_sub (X Y Z Z' : R) :
    MvPolynomial.eval ![X, Y, Z] W.toProjective.polynomial -
        MvPolynomial.eval ![X, Y, Z'] W.toProjective.polynomial =
      (Z - Z') * infinityCubicDividedZ W X Y Z Z' := by
  simp only [Projective.eval_polynomial, Projective.fin3_def_ext, infinityCubicDividedZ]
  ring

/-- Two arbitrary line cubics differ by their linear separation times a quadratic. -/
theorem infinityLineCubic_sub (l m b c X Y : R) :
    MvPolynomial.eval ![X, Y, l * X + b * Y] W.toProjective.polynomial -
        MvPolynomial.eval ![X, Y, m * X + c * Y] W.toProjective.polynomial =
      ((l - m) * X + (b - c) * Y) *
        infinityCubicDividedZ W X Y (l * X + b * Y) (m * X + c * Y) := by
  rw [infinityCubic_sub]
  congr 1
  ring

/-- The quadratic differences satisfy the three-line telescoping identity. -/
theorem infinityCubicDividedZ_cocycle (X Y Z₁ Z₂ Z₃ : R) :
    (Z₁ - Z₂) * infinityCubicDividedZ W X Y Z₁ Z₂ +
        (Z₂ - Z₃) * infinityCubicDividedZ W X Y Z₂ Z₃ =
      (Z₁ - Z₃) * infinityCubicDividedZ W X Y Z₁ Z₃ := by
  rw [← infinityCubic_sub, ← infinityCubic_sub, ← infinityCubic_sub]
  ring

end FLT.Mazur.WeierstrassIntegralChart
