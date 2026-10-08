/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityQuadraticLift

/-!
# Homogeneous pencils after coefficient extension

Map coefficients before lifting a quadratic. This transports polynomial identities
to common polynomial parameters without reasoning from their scalar evaluations.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

/-- Coefficient extension followed by homogeneous quadratic evaluation. -/
def infinityQuadraticBaseChange (p : R[X]) (U V : S) : S :=
  infinityQuadraticLift (p.map f) U V

/-- Subtraction commutes with the coefficient extension and homogeneous lift. -/
theorem infinityQuadraticBaseChange_sub (p q : R[X]) (U V : S) :
    infinityQuadraticBaseChange f (p - q) U V =
      infinityQuadraticBaseChange f p U V - infinityQuadraticBaseChange f q U V := by
  simp only [infinityQuadraticBaseChange, Polynomial.map_sub, infinityQuadraticLift_sub]

/-- A scalar multiplier is mapped once before being taken outside the lift. -/
theorem infinityQuadraticBaseChange_C_mul (c : R) (p : R[X]) (U V : S) :
    infinityQuadraticBaseChange f (C c * p) U V =
      f c * infinityQuadraticBaseChange f p U V := by
  simp only [infinityQuadraticBaseChange, Polynomial.map_mul, map_C,
    infinityQuadraticLift_C_mul]

/-- Both linear factors survive arbitrary coefficient extension. -/
theorem infinityQuadraticBaseChange_factors (a n u : R) (U V : S) :
    infinityQuadraticBaseChange f ((X - C a) * (C n * X - C u)) U V =
      (U - f a * V) * (f n * U - f u * V) := by
  simp only [infinityQuadraticBaseChange, Polynomial.map_mul, Polynomial.map_sub,
    map_C, map_X, infinityQuadraticLift_factors]

/-- The pencil correction becomes the same divided cubic over the new coefficient ring. -/
theorem infinityQuadraticBaseChange_denominator (W : WeierstrassCurve R)
    (x z l m : R) (U V : S) :
    infinityQuadraticBaseChange f (infinitySlopeDenominator (W.map C) X
      (C z + C l * (X - C x)) (C z + C m * (X - C x))) U V =
      infinityCubicDividedZ (W.map f) U V (f z * V + f l * (U - f x * V))
        (f z * V + f m * (U - f x * V)) := by
  unfold infinityQuadraticBaseChange
  have h : (infinitySlopeDenominator (W.map C) X
      (C z + C l * (X - C x)) (C z + C m * (X - C x))).map f =
      infinitySlopeDenominator ((W.map f).map C) X
        (C (f z) + C (f l) * (X - C (f x)))
        (C (f z) + C (f m) * (X - C (f x))) := by
    simp only [infinitySlopeDenominator, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
      WeierstrassCurve.map_a₆, Polynomial.map_sub, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_one, map_X, map_C]
  rw [h, infinityQuadraticLift_denominator]

end FLT.Mazur.WeierstrassIntegralChart
