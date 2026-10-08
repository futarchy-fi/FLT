/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLineCubicFactorization
public import FLT.Mazur.WeierstrassInfinityNormalizedLine

/-!
# Cubic splitting on the actual infinity addition domain

The normalizing factor is the constructed, invertible output Y coordinate.
The identities specialize along every coefficient algebra map, so they apply
to each of the four laws on the genuine all-infinity triple intersection.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve MvPolynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (f : InfinityAdditionOpen W →ₐ[R] S)

/-- The actual left input satisfies the cubic in every coefficient algebra. -/
theorem infinitySpecialization_left_equation :
    (W.map (algebraMap R S)).toProjective.Equation
      ![f (infinityInputLeft W (coord W 1 0)), 1,
        f (infinityInputLeft W (coord W 1 2))] :=
  infinityLeft_equation W (f.comp (infinityAdditionRestriction W))

/-- The actual right input satisfies the cubic in every coefficient algebra. -/
theorem infinitySpecialization_right_equation :
    (W.map (algebraMap R S)).toProjective.Equation
      ![f (infinityInputRight W (coord W 1 0)), 1,
        f (infinityInputRight W (coord W 1 2))] :=
  infinityRight_equation W (f.comp (infinityAdditionRestriction W))

/-- The genuine output supplies a third linear factor, with its unit kept explicit. -/
theorem infinitySpecialization_factorization (X Y : S) :
    let V := W.map (algebraMap R S)
    let x₁ := f (infinityInputLeft W (coord W 1 0))
    let x₂ := f (infinityInputRight W (coord W 1 0))
    let z₁ := f (infinityInputLeft W (coord W 1 2))
    let m := f (infinityChartSlope W)
    let x := f (infinityAdditionChart W (coord W 1 0))
    let z := f (infinityAdditionChart W (coord W 1 2))
    let u := f (infinityOutputRestriction W (infinityOutputCoordinates W 1))
    eval ![X, Y, m * X + (z₁ - m * x₁) * Y] V.toProjective.polynomial =
      u * (X - x₁ * Y) * (X - x₂ * Y) *
        ((-1 - V.a₁ * x - V.a₃ * z) * X - x * Y) := by
  apply infinityLine_normalized_factorization _
    (infinitySpecialization_left_equation W f)
    (infinitySpecialization_line W f) (infinitySpecialization_cubic W f)
  · rw [infinitySpecialization_homogeneous W f 1]
    exact infinitySpecialization_coord_mul W f 0
  · exact infinitySpecialization_output_negY W f

/-- The last factor's two coefficients generate the unit ideal, even if Y is not a unit. -/
theorem infinitySpecialization_third_unimodular :
    let V := W.map (algebraMap R S)
    let x := f (infinityAdditionChart W (coord W 1 0))
    let z := f (infinityAdditionChart W (coord W 1 2))
    let m := f (infinityChartSlope W)
    let b := f (infinityInputLeft W (coord W 1 2)) -
      m * f (infinityInputLeft W (coord W 1 0))
    (-1 - V.a₁ * x - V.a₃ * z) * (-(1 + V.a₃ * b)) +
      x * (-(V.a₁ + V.a₃ * m)) = 1 := by
  dsimp only
  have h := infinitySpecialization_output_line W f
  dsimp only at h
  linear_combination (W.map (algebraMap R S)).a₃ * h

end FLT.Mazur.WeierstrassIntegralChart
