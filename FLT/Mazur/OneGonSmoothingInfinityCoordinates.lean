/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingEquation
public import FLT.Mazur.WeierstrassIntegralChart
public import FLT.Mazur.LaurentUnitPoints

/-!
# Explicit torus coordinates on the zero-parameter infinity chart

Writing a = X/Y and b = Z/Y gives (1-a)b = a³. Thus 1-a is a unit
with inverse 1+a+a²+b. The original torus coordinate is its inverse.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart WeierstrassCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R]

/-- The relation at infinity of the original nodal cubic. -/
theorem zeroInfinity_relation :
    (1 - coord (equation (0 : R)) 1 0) * coord (equation (0 : R)) 1 2 =
      coord (equation (0 : R)) 1 0 ^ 3 := by
  have h := coord_equation (equation (0 : R)) 1
  rw [Projective.equation_iff] at h
  simp only [coord_self] at h
  dsimp only [WeierstrassCurve.toProjective, WeierstrassCurve.map, equation] at h
  simp only [map_neg, map_one, map_zero] at h
  dsimp only [equation]
  linear_combination h

/-- The inverse of 1-X/Y is a polynomial in the two chart coordinates. -/
def zeroInfinityParameter : (Coordinate (equation (0 : R)) 1)ˣ where
  val := 1 + coord (equation (0 : R)) 1 0 + coord (equation (0 : R)) 1 0 ^ 2 +
    coord (equation (0 : R)) 1 2
  inv := 1 - coord (equation (0 : R)) 1 0
  val_inv := by linear_combination zeroInfinity_relation (R := R)
  inv_val := by linear_combination zeroInfinity_relation (R := R)

/-- Evaluate the original multiplicative coordinate on the infinity chart. -/
def torusToZeroInfinity : R[T;T⁻¹] →ₐ[R] Coordinate (equation (0 : R)) 1 :=
  LaurentUnitPoints.evalUnit zeroInfinityParameter

/-- The positive torus coordinate is the specified polynomial inverse. -/
@[simp] theorem torusToZeroInfinity_T :
    torusToZeroInfinity (LaurentPolynomial.T 1 : R[T;T⁻¹]) =
      1 + coord (equation (0 : R)) 1 0 + coord (equation (0 : R)) 1 0 ^ 2 +
        coord (equation (0 : R)) 1 2 := by
  simp [torusToZeroInfinity, zeroInfinityParameter]

/-- The inverse torus coordinate is exactly 1-X/Y. -/
@[simp] theorem torusToZeroInfinity_T_neg :
    torusToZeroInfinity (LaurentPolynomial.T (-1) : R[T;T⁻¹]) =
      1 - coord (equation (0 : R)) 1 0 := by
  simp [torusToZeroInfinity, zeroInfinityParameter]

/-- The original Laurent coordinate gives a normalized point of the infinity chart. -/
theorem torusInfinity_equation :
    ((equation (0 : R)).map (algebraMap R R[T;T⁻¹])).toProjective.Equation
      ![1 - LaurentPolynomial.T (-1), 1,
        LaurentPolynomial.T 1 * (1 - LaurentPolynomial.T (-1)) ^ 3] := by
  rw [Projective.equation_iff]
  simp only [Projective.fin3_def_ext]
  dsimp only [WeierstrassCurve.toProjective, WeierstrassCurve.map, equation]
  simp only [map_neg, map_one, map_zero]
  have ht : (LaurentPolynomial.T 1 : R[T;T⁻¹]) * LaurentPolynomial.T (-1) = 1 := by
    rw [← LaurentPolynomial.T_add]
    norm_num
  linear_combination (1 - LaurentPolynomial.T (-1)) ^ 3 * ht

/-- The explicit map from the infinity chart to the original Laurent algebra. -/
def zeroInfinityToTorus : Coordinate (equation (0 : R)) 1 →ₐ[R] R[T;T⁻¹] :=
  evaluation _ 1 ![1 - LaurentPolynomial.T (-1), 1,
    LaurentPolynomial.T 1 * (1 - LaurentPolynomial.T (-1)) ^ 3]
      torusInfinity_equation rfl

/-- The first chart coordinate is 1 minus the inverse torus coordinate. -/
@[simp] theorem zeroInfinityToTorus_x :
    zeroInfinityToTorus (coord (equation (0 : R)) 1 0) =
      1 - LaurentPolynomial.T (-1) := by
  simp [zeroInfinityToTorus]

/-- The last chart coordinate is the specified cubic Laurent expression. -/
@[simp] theorem zeroInfinityToTorus_z :
    zeroInfinityToTorus (coord (equation (0 : R)) 1 2) =
      LaurentPolynomial.T 1 * (1 - LaurentPolynomial.T (-1)) ^ 3 := by
  simp [zeroInfinityToTorus]

end FLT.Mazur.OneGonSmoothing
