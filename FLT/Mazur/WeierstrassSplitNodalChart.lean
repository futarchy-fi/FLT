/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralChart
public import FLT.Mazur.LaurentUnitPoints

/-!
# The infinity chart of a split nodal cubic

For a unit a, the equation Y²Z+aXYZ=X³ has infinity chart
Z(1+aX)=X³. The tangent factor 1+aX has an explicit polynomial inverse,
so this chart admits actual mutually inverse Laurent coordinates.
-/

@[expose] public noncomputable section

open scoped LaurentPolynomial

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (a : Rˣ)

/-- The split nodal integral equation with invertible tangent separation. -/
def splitNodalEquation : WeierstrassCurve R := ⟨a, 0, 0, 0, 0⟩

/-- The actual equation on its normalized infinity chart. -/
theorem splitNodalChart_relation :
    coord (splitNodalEquation a) 1 2 *
        (1 + algebraMap R _ a * coord (splitNodalEquation a) 1 0) =
      coord (splitNodalEquation a) 1 0 ^ 3 := by
  have h := coord_equation (splitNodalEquation a) 1
  rw [WeierstrassCurve.Projective.equation_iff] at h
  change coord (splitNodalEquation a) 1 1 ^ 2 * coord (splitNodalEquation a) 1 2 +
    algebraMap R _ a * coord (splitNodalEquation a) 1 0 *
      coord (splitNodalEquation a) 1 1 * coord (splitNodalEquation a) 1 2 +
    algebraMap R _ 0 * coord (splitNodalEquation a) 1 1 *
      coord (splitNodalEquation a) 1 2 ^ 2 -
    (coord (splitNodalEquation a) 1 0 ^ 3 +
      algebraMap R _ 0 * coord (splitNodalEquation a) 1 0 ^ 2 *
        coord (splitNodalEquation a) 1 2 +
      algebraMap R _ 0 * coord (splitNodalEquation a) 1 0 *
        coord (splitNodalEquation a) 1 2 ^ 2 +
      algebraMap R _ 0 * coord (splitNodalEquation a) 1 2 ^ 3) = 0 at h
  simp only [coord_self, map_zero, zero_mul, one_pow, mul_one, one_mul, add_zero] at h
  linear_combination h

/-- The inverse of the tangent factor, written as a polynomial in chart coordinates. -/
def splitNodalTangentInverse : Coordinate (splitNodalEquation a) 1 :=
  1 - algebraMap R _ a * coord (splitNodalEquation a) 1 0 +
    (algebraMap R _ a * coord (splitNodalEquation a) 1 0) ^ 2 -
      algebraMap R _ a ^ 3 * coord (splitNodalEquation a) 1 2

/-- The cubic relation proves that the two tangent factors are inverse. -/
theorem splitNodalTangent_mul_inverse :
    (1 + algebraMap R _ a * coord (splitNodalEquation a) 1 0) *
      splitNodalTangentInverse a = 1 := by
  dsimp only [splitNodalTangentInverse]
  linear_combination -(algebraMap R (Coordinate (splitNodalEquation a) 1) a) ^ 3 *
    splitNodalChart_relation a

/-- The tangent factor is an actual unit in the original infinity chart algebra. -/
def splitNodalTangentUnit : (Coordinate (splitNodalEquation a) 1)ˣ where
  val := 1 + algebraMap R _ a * coord (splitNodalEquation a) 1 0
  inv := splitNodalTangentInverse a
  val_inv := splitNodalTangent_mul_inverse a
  inv_val := by rw [mul_comm]; exact splitNodalTangent_mul_inverse a

/-- Laurent evaluation in the actual nodal infinity chart. -/
def splitNodalLaurentToChart : R[T;T⁻¹] →ₐ[R] Coordinate (splitNodalEquation a) 1 :=
  LaurentUnitPoints.evalUnit (splitNodalTangentUnit a)

/-- The positive Laurent generator is the tangent factor. -/
@[simp] theorem splitNodalLaurentToChart_pos :
    splitNodalLaurentToChart a (LaurentPolynomial.T 1) =
      1 + algebraMap R _ a * coord (splitNodalEquation a) 1 0 := by
  simp [splitNodalLaurentToChart, splitNodalTangentUnit]

/-- The negative Laurent generator is the explicit polynomial inverse. -/
@[simp] theorem splitNodalLaurentToChart_neg :
    splitNodalLaurentToChart a (LaurentPolynomial.T (-1)) = splitNodalTangentInverse a := by
  simp [splitNodalLaurentToChart, splitNodalTangentUnit]

/-- The X coordinate is recovered from the tangent factor using its unit coefficient. -/
theorem splitNodalChart_x_recovery :
    algebraMap R _ (↑(a⁻¹) : R) *
      ((1 + algebraMap R _ a * coord (splitNodalEquation a) 1 0) - 1) =
        coord (splitNodalEquation a) 1 0 := by
  simp only [add_sub_cancel_left, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

/-- The Z coordinate is recovered from X and the inverse tangent factor. -/
theorem splitNodalChart_z_recovery :
    coord (splitNodalEquation a) 1 0 ^ 3 * splitNodalTangentInverse a =
      coord (splitNodalEquation a) 1 2 := by
  rw [← splitNodalChart_relation, mul_assoc, splitNodalTangent_mul_inverse, mul_one]

end FLT.Mazur.WeierstrassIntegralChart
