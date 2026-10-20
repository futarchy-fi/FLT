/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationShear
public import FLT.Mazur.WeierstrassDividedTangentBranchSource

/-!
# Construct sheared branch inputs from original divided inputs

The input maps are transported by the actual divided coordinate equivalence.
The two branch factors change by explicit multiples of the shear parameter.
Consequently their specializations agree whenever that parameter vanishes.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassDividedDepth
attribute [local irreducible] rootShearCurve
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 r : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "V" => rootShearCurve W r
local notation "A" => Coordinate V s b3 (b4 - r * b3) b6
local notation "q" => algebraMap R S r

/-- The original input expressed in the actual sheared divided coordinates. -/
def branchShearInput : A →ₐ[R] S := a.comp (shearBackward W s b3 b4 b6 r)

/-- The abscissa of an original input is unchanged. -/
theorem branchShearInput_x :
    branchShearInput W s b3 b4 b6 r a (x V s b3 (b4 - r * b3) b6) =
      a (x W s b3 b4 b6) := by
  simp [branchShearInput]

/-- The ordinate has the exact integral shear correction. -/
theorem branchShearInput_y :
    branchShearInput W s b3 b4 b6 r a (y V s b3 (b4 - r * b3) b6) =
      a (y W s b3 b4 b6) - q * a (x W s b3 b4 b6) := by
  simp [branchShearInput]

local notation "a'" => branchShearInput W s b3 b4 b6 r a
local notation "c'" => branchShearInput W s b3 b4 b6 r c

/-- The first branch factor changes by the shear times the first abscissa. -/
theorem branchShearInput_factor :
    dividedTangentBranchFactor V s b3 (b4 - r * b3) b6 a' =
      dividedTangentBranchFactor W s b3 b4 b6 a + q * a (x W s b3 b4 b6) := by
  simp only [dividedTangentBranchFactor, branchShearInput_x, branchShearInput_y,
    (rootShearCurve_coefficients r).1, map_add, map_mul, map_ofNat]
  ring

/-- The tangent denominator changes by the shear times the abscissa difference. -/
theorem branchShearInput_denominator :
    dividedTangentDenominator V s b3 (b4 - r * b3) b6 a' c' =
      dividedTangentDenominator W s b3 b4 b6 a c +
        q * (c (x W s b3 b4 b6) - a (x W s b3 b4 b6)) := by
  simp only [dividedTangentDenominator, branchShearInput_x, branchShearInput_y,
    (rootShearCurve_coefficients r).1, map_add, map_mul, map_ofNat]
  ring

/-- Both actual branch factors specialize to the original ones when the shear vanishes. -/
theorem branchShearInput_specialization {T : Type*} [CommRing T] (f : S →+* T)
    (hr : f q = 0) :
    f (dividedTangentBranchFactor V s b3 (b4 - r * b3) b6 a') =
        f (dividedTangentBranchFactor W s b3 b4 b6 a) ∧
      f (dividedTangentDenominator V s b3 (b4 - r * b3) b6 a' c') =
        f (dividedTangentDenominator W s b3 b4 b6 a c) := by
  simp only [branchShearInput_factor, branchShearInput_denominator,
    map_add, map_mul, hr, zero_mul, add_zero, and_self]

end FLT.Mazur.WeierstrassDilatation
