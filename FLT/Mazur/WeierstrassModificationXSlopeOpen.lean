/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXAlgebra
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The full slope open at scale one

The equation t*v*(v+a)=1 is the polynomial slope line with both tangent
factors inverted. Its actual denominator and inverse are retained explicitly.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (a : R)

/-- The product of the two ordered tangent slopes. -/
def slopePolynomial : R[X] := X * (X + C a)
/-- The entire slope line with both tangent slopes removed. -/
abbrev SlopeOpen := Localization.Away (slopePolynomial a)
/-- The polynomial slope coordinate. -/
def slopeZ : SlopeOpen a := algebraMap R[X] _ X
/-- The inverse of the product of the two tangent factors. -/
def slopeInv : SlopeOpen a := IsLocalization.Away.invSelf (slopePolynomial a)

/-- The original horizontal function is the product of the two slope factors. -/
theorem slopePolynomial_map :
    algebraMap R[X] (SlopeOpen a) (slopePolynomial a) =
      slopeZ a * (slopeZ a + algebraMap R _ a) := by
  have hc : algebraMap R[X] (SlopeOpen a) (C a) = algebraMap R _ a :=
    (IsScalarTower.algebraMap_apply R R[X] (SlopeOpen a) a).symm
  simp only [slopePolynomial, map_mul, map_add, slopeZ, hc]

/-- The entire product has an inverse on this open, including both factors. -/
theorem slope_mul_inv :
    (slopeZ a * (slopeZ a + algebraMap R _ a)) * slopeInv a = 1 := by
  rw [← slopePolynomial_map]
  exact IsLocalization.Away.mul_invSelf (slopePolynomial a)

/-- Both tangent factors and the incidence parameter are units on this whole chart. -/
theorem slope_units :
    IsUnit (slopeZ a) ∧ IsUnit (slopeZ a + algebraMap R _ a) ∧ IsUnit (slopeInv a) := by
  have h : IsUnit ((slopeZ a * (slopeZ a + algebraMap R _ a)) * slopeInv a) := by
    rw [slope_mul_inv]
    exact isUnit_one
  exact ⟨isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h),
    isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left h),
    isUnit_of_mul_isUnit_right h⟩

end FLT.Mazur.WeierstrassModificationX
