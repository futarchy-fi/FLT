/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Ring.Units
public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Data.Nat.Cast.Basic

/-!
# Exact division by a natural number that is a unit

The inverse to multiplication by a unit natural number is additive and commutes
with ring maps. These formulas allow transfer degrees to be removed without
assuming the ambient ring is reduced or torsion-free.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.UnitNaturalDivision
variable {R S : Type*} [CommRing R] [CommRing S] (n : ℕ) (h : IsUnit (n : R))

/-- Division by a unit natural number, as an additive map on the whole ring. -/
def divide : R →+ R where
  toFun x := ↑h.unit⁻¹ * x
  map_zero' := mul_zero _
  map_add' _ _ := mul_add _ _ _

/-- Multiplication by the degree recovers the original section exactly. -/
theorem nsmul_divide (x : R) : n • divide n h x = x := by
  change n • (↑h.unit⁻¹ * x) = x
  simpa only [nsmul_eq_mul, h.unit_spec] using h.unit.mul_inv_cancel_left x

include h in
/-- A unit degree can be canceled even in a ring with nilpotents. -/
theorem nsmul_injective : Function.Injective (fun x : R ↦ n • x) := by
  intro x y hh
  simp only [nsmul_eq_mul] at hh
  exact h.mul_left_cancel hh

/-- Division is also a left inverse to multiplication by the degree. -/
theorem divide_nsmul (x : R) : divide n h (n • x) = x := by
  apply nsmul_injective n h
  dsimp only
  rw [nsmul_divide]

include h in
/-- Ring maps transport the invertibility of the natural degree. -/
theorem isUnit_map (f : R →+* S) : IsUnit (n : S) := by
  simpa only [map_natCast] using h.map f

/-- Division commutes with any ring map, independently of the unit witnesses. -/
theorem map_divide (f : R →+* S) (hS : IsUnit (n : S)) (x : R) :
    f (divide n h x) = divide n hS (f x) := by
  apply nsmul_injective n hS
  dsimp only
  rw [← map_nsmul, nsmul_divide, nsmul_divide]

/-- A scaled image equation yields the exact unscaled image after division. -/
theorem map_divide_eq (f : R →+* S) (x : R) (y : S)
    (hx : f x = n • y) : f (divide n h x) = y := by
  rw [map_divide n h f (isUnit_map n h f), hx, divide_nsmul]

/-- A section error vanishes after division exactly when it vanished beforehand. -/
theorem divide_eq_iff (x y : R) : divide n h x = y ↔ x = n • y := by
  constructor
  · intro hh
    rw [← hh, nsmul_divide]
  · intro hh
    rw [hh, divide_nsmul]

end FLT.Mazur.UnitNaturalDivision
