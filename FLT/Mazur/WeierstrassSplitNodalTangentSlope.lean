/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralAdditionFormula
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# The genuine secant slope at a first-order split node

A smooth affine parameter has coordinates `r q, r² q`, where `q = r + a`.
For square-zero node coordinates the slope is explicit over arbitrary rings.
This is the local calculation needed for the action on the initial exceptional conic.
-/

@[expose] public section
namespace FLT.Mazur.WeierstrassIntegralChart
variable {S : Type*} [CommRing S] (r q : Sˣ) (x y : S)

/-- The first-order displacement of the ordinary secant slope. -/
def splitNodalTangentDisplacement : S :=
  (↑r⁻¹ : S) * (↑q⁻¹ : S) * ((r : S) * x - y)

/-- The secant slope from a smooth affine point to an infinitesimal node point. -/
def splitNodalTangentSlope : S := (r : S) + splitNodalTangentDisplacement r q x y

/-- Clearing the two unit denominators gives the first-order numerator. -/
theorem splitNodalTangentDisplacement_denominator :
    (r : S) * q * splitNodalTangentDisplacement r q x y = (r : S) * x - y := by
  simp only [splitNodalTangentDisplacement]
  calc
    _ = ((r : S) * ↑r⁻¹) * ((q : S) * ↑q⁻¹) * ((r : S) * x - y) := by ring
    _ = _ := by rw [Units.mul_inv, Units.mul_inv, one_mul, one_mul]


/-- The slope displacement annihilates the infinitesimal X coordinate. -/
theorem splitNodalTangentDisplacement_mul_x (hxx : x ^ 2 = 0) (hxy : x * y = 0) :
    splitNodalTangentDisplacement r q x y * x = 0 := by
  dsimp [splitNodalTangentDisplacement]
  linear_combination (↑r⁻¹ : S) * (↑q⁻¹ : S) * ((r : S) * hxx - hxy)

/-- The slope displacement annihilates the infinitesimal Y coordinate. -/
theorem splitNodalTangentDisplacement_mul_y (hxy : x * y = 0) (hyy : y ^ 2 = 0) :
    splitNodalTangentDisplacement r q x y * y = 0 := by
  dsimp [splitNodalTangentDisplacement]
  linear_combination (↑r⁻¹ : S) * (↑q⁻¹ : S) * ((r : S) * hxy - hyy)

/-- The slope displacement is itself square-zero. -/
theorem splitNodalTangentDisplacement_sq
    (hxx : x ^ 2 = 0) (hxy : x * y = 0) (hyy : y ^ 2 = 0) :
    splitNodalTangentDisplacement r q x y ^ 2 = 0 := by
  dsimp [splitNodalTangentDisplacement]
  linear_combination
    ((↑r⁻¹ : S) * (↑q⁻¹ : S)) ^ 2 *
      ((r : S) ^ 2 * hxx - 2 * (r : S) * hxy + hyy)

/-- The explicit slope satisfies the actual ordinary secant relation. -/
theorem splitNodalTangentSlope_line (hxx : x ^ 2 = 0) (hxy : x * y = 0) :
    splitNodalTangentSlope r q x y * ((r : S) * q - x) = (r : S) ^ 2 * q - y := by
  have hd := splitNodalTangentDisplacement_denominator r q x y
  have hx := splitNodalTangentDisplacement_mul_x r q x y hxx hxy
  dsimp only [splitNodalTangentSlope]
  linear_combination hd - hx

/-- The secant denominator stays a unit on all square-zero node points. -/
theorem splitNodalTangent_denominator_isUnit (hxx : x ^ 2 = 0) : IsUnit ((r : S) * q - x) := by
  have hx : IsNilpotent x := ⟨2, hxx⟩
  simpa only [sub_eq_add_neg, Units.val_mul] using
    hx.neg.isUnit_add_left_of_commute (r * q).isUnit (Commute.all _ _)

/-- Any actual secant slope on these inputs equals the explicit first-order slope. -/
theorem splitNodalTangentSlope_unique (hxx : x ^ 2 = 0) (hxy : x * y = 0) (l : S)
    (hl : l * ((r : S) * q - x) = (r : S) ^ 2 * q - y) :
    l = splitNodalTangentSlope r q x y := by
  apply (splitNodalTangent_denominator_isUnit r q x hxx).mul_left_inj.mp
  exact hl.trans (splitNodalTangentSlope_line r q x y hxx hxy).symm

end FLT.Mazur.WeierstrassIntegralChart
