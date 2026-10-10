/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.Tactic.LinearCombination

/-!
# A coordinate frame detects a Weierstrass change of variables

Three fixed affine points force a change of variables to be the identity when
one horizontal difference and one vertical difference are units. This works
over arbitrary rings, including nonreduced rings, without dividing by three.
-/

@[expose] public section

open WeierstrassCurve

namespace FLT.Mazur.WeierstrassVariableChangeFrame

variable {R : Type*} [CommRing R]

/-- Two points over one abscissa and a third over a unit-separated abscissa
rigidify an admissible change of variables over an arbitrary ring. -/
theorem eq_one (C : VariableChange R) (x y y' z w : R)
    (hxz : IsUnit (x - z)) (hyy : IsUnit (y - y'))
    (hx : (C.u : R) ^ 2 * x + C.r = x)
    (hz : (C.u : R) ^ 2 * z + C.r = z)
    (hy : (C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t = y)
    (hy' : (C.u : R) ^ 3 * y' + (C.u : R) ^ 2 * C.s * x + C.t = y')
    (hw : (C.u : R) ^ 3 * w + (C.u : R) ^ 2 * C.s * z + C.t = w) :
    C = 1 := by
  have hu2 : (C.u : R) ^ 2 = 1 := by
    apply sub_eq_zero.mp
    apply (hxz.mul_left_eq_zero).mp
    linear_combination hx - hz
  have hu3 : (C.u : R) ^ 3 = 1 := by
    apply sub_eq_zero.mp
    apply (hyy.mul_left_eq_zero).mp
    linear_combination hy - hy'
  have hu : (C.u : R) = 1 := by
    linear_combination hu3 - (C.u : R) * hu2
  have hr : C.r = 0 := by simpa only [hu, one_pow, one_mul, add_eq_left] using hx
  have hs : C.s = 0 := by
    apply (hxz.mul_left_eq_zero).mp
    linear_combination hy - hw - (y - w + C.s * (x - z)) * hu2 +
      (y - w) * (hu2 - hu3)
  have ht : C.t = 0 := by
    simpa only [hu, hs, one_pow, one_mul, zero_mul, add_zero, add_eq_left] using hy
  apply VariableChange.ext
  · exact Units.ext hu
  · exact hr
  · exact hs
  · exact ht

end FLT.Mazur.WeierstrassVariableChangeFrame
