/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalTangentSlope

/-!
# The two tangent characters of actual nodal addition

The branch coordinates `y` and `y + a*x` transform by reciprocal characters.
The formulas use the genuine affine addition polynomials over arbitrary rings,
including rings with nilpotents; they do not posit an action on exceptional components.
-/

@[expose] public section
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassCurve
variable {S : Type*} [CommRing S] (a : S) (r q : Sˣ) (x y : S)
local notation "W" => WeierstrassCurve.mk a 0 0 0 0
local notation "d" => splitNodalTangentDisplacement r q x y
local notation "l" => splitNodalTangentSlope r q x y
local notation "X" => Affine.addX (toAffine W) ((r : S) * q) x l
local notation "Y" => Affine.addY (toAffine W) ((r : S) * q) x ((r : S) ^ 2 * q) l

/-- The actual X addition polynomial has the expected first-order expansion. -/
theorem splitNodalTangent_addX (hq : (q : S) = (r : S) + a)
    (hxx : x ^ 2 = 0) (hxy : x * y = 0) (hyy : y ^ 2 = 0) :
    X = ((r : S) + q) * d - x := by
  have hd := splitNodalTangentDisplacement_sq r q x y hxx hxy hyy
  dsimp only [Affine.addX, toAffine, splitNodalTangentSlope]
  linear_combination hd - ((r : S) + d) * hq

/-- The actual Y addition polynomial has the expected first-order expansion. -/
theorem splitNodalTangent_addY (hq : (q : S) = (r : S) + a)
    (hxx : x ^ 2 = 0) (hxy : x * y = 0) (hyy : y ^ 2 = 0) :
    Y = (q : S) * x - (q : S) ^ 2 * d := by
  have hx := splitNodalTangent_addX a r q x y hq hxx hxy hyy
  have hd := splitNodalTangentDisplacement_sq r q x y hxx hxy hyy
  have hdx := splitNodalTangentDisplacement_mul_x r q x y hxx hxy
  dsimp only [Affine.addY, Affine.negY, Affine.negAddY, toAffine]
  rw [hx]
  dsimp only [splitNodalTangentSlope]
  linear_combination -((r : S) + q) * hd + hdx +
    (((r : S) + q) * d - x) * hq

/-- The first branch equation is an eigenvector for the genuine tangent action. -/
theorem splitNodalTangent_first_character (hq : (q : S) = (r : S) + a)
    (hxx : x ^ 2 = 0) (hxy : x * y = 0) (hyy : y ^ 2 = 0) :
    (r : S) * Y = (q : S) * y := by
  rw [splitNodalTangent_addY a r q x y hq hxx hxy hyy]
  have hd := splitNodalTangentDisplacement_denominator r q x y
  linear_combination -(q : S) * hd

/-- The opposite branch equation has the reciprocal character. -/
theorem splitNodalTangent_second_character (hq : (q : S) = (r : S) + a)
    (hxx : x ^ 2 = 0) (hxy : x * y = 0) (hyy : y ^ 2 = 0) :
    (q : S) * (Y + a * X) = (r : S) * (y + a * x) := by
  rw [splitNodalTangent_addY a r q x y hq hxx hxy hyy,
    splitNodalTangent_addX a r q x y hq hxx hxy hyy]
  have hd := splitNodalTangentDisplacement_denominator r q x y
  linear_combination -(r : S) * hd +
    (((q : S) + r) * x - ((q : S) + r) * q * d) * hq

end FLT.Mazur.WeierstrassIntegralChart
