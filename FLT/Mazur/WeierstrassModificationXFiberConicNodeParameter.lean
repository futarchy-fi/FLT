/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicFirstParameter

/-!
# Node coordinates on the original full fiber near the first incidence section

On the actual open v+a invertible put z=t/(v+a) and w=v-c*z²*(v+a).
The full fiber equation gives z*w=0. The parameter denominator 1-c*z²
is a unit when a is a unit, without discarding the conic component.
The inverse node-chart equivalence is a separate construction.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (a c : R)

/-- The first actual tangent open of the entire fiber, retaining c. -/
abbrev FullFirstFiberOpen := Localization.Away (fiberV a c + algebraMap R _ a)
local notation "F" => FiberCoordinate a c
local notation "O" => FullFirstFiberOpen a c
local notation "U" => algebraMap F O (fiberV a c + algebraMap R F a)
local notation "T" => algebraMap F O (fiberT a c)
local notation "V" => algebraMap F O (fiberV a c)
local notation "A" => algebraMap R O a
local notation "C" => algebraMap R O c

/-- The incidence parameter on the entire fiber neighborhood. -/
def fullFirstFiberParameter : O :=
  T * IsLocalization.Away.invSelf (fiberV a c + algebraMap R F a)
local notation "z" => fullFirstFiberParameter a c

/-- The corrected slope that vanishes on the conic component. -/
def fullFirstFiberNodeSlope : O := V - C * z ^ 2 * U
local notation "w" => fullFirstFiberNodeSlope a c

/-- The incidence parameter retains its original denominator. -/
theorem fullFirstFiberParameter_mul : z * U = T := by
  rw [fullFirstFiberParameter]
  calc (T * IsLocalization.Away.invSelf (fiberV a c + algebraMap R F a)) * U =
      T * (U * IsLocalization.Away.invSelf (fiberV a c + algebraMap R F a)) := by ring
    _ = T := by rw [IsLocalization.Away.mul_invSelf, mul_one]

/-- The entire original fiber satisfies the node equation in these coordinates. -/
theorem fullFirstFiber_node_relation : z * w = 0 := by
  have h : T * (V * U - C * T ^ 2) = 0 := by
    have h := congrArg (algebraMap F O) (fiber_relation a c)
    simpa only [map_mul, map_sub, map_pow, map_zero,
      ← IsScalarTower.algebraMap_apply R F O] using h
  apply ((IsLocalization.Away.algebraMap_isUnit
    (S := O) (fiberV a c + algebraMap R F a)).pow 2).mul_right_cancel
  rw [zero_mul]
  calc z * w * U ^ 2 = T * (V * U - C * T ^ 2) := by
        rw [← fullFirstFiberParameter_mul]
        dsimp [fullFirstFiberNodeSlope]
        ring
    _ = 0 := h

/-- The node correction gives the exact parameter denominator identity. -/
theorem fullFirstFiber_denominator_mul : (1 - C * z ^ 2) * U = w + A := by
  have hu : U = V + A := by
    rw [map_add, ← IsScalarTower.algebraMap_apply R F O]
  dsimp [fullFirstFiberNodeSlope]
  rw [hu]
  ring

/-- Multiplication by the parameter denominator fixes the node slope. -/
theorem fullFirstFiber_denominator_slope : (1 - C * z ^ 2) * w = w := by
  calc (1 - C * z ^ 2) * w = w - C * z * (z * w) := by ring
    _ = w := by rw [fullFirstFiber_node_relation, mul_zero, sub_zero]

/-- A unit tangent difference makes the parameter denominator a unit on the full open. -/
theorem fullFirstFiber_denominator_isUnit (ha : IsUnit a) : IsUnit (1 - C * z ^ 2) := by
  have h : (1 - C * z ^ 2) * (U - w) = A := by
    rw [mul_sub, fullFirstFiber_denominator_mul, fullFirstFiber_denominator_slope,
      add_sub_cancel_left]
  exact isUnit_of_mul_isUnit_left (h ▸ ha.map (algebraMap R O))

/-- The corrected opposite tangent factor is invertible as required for the node open. -/
theorem fullFirstFiber_nodeDenominator_isUnit (ha : IsUnit a) : IsUnit (w + A) := by
  rw [← fullFirstFiber_denominator_mul]
  exact (fullFirstFiber_denominator_isUnit a c ha).mul
    (IsLocalization.Away.algebraMap_isUnit (fiberV a c + algebraMap R F a))

end FLT.Mazur.WeierstrassModificationX
