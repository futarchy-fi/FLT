/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberAlgebra
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Fractional coordinates on a full smoothing-node tangent open

On D(q+a), the coordinate q/(q+a) sends the deleted opposite tangent to
infinity. Its difference from one is a unit when a is a unit. This is the
fractional coordinate needed to turn opposite initial reflection into inversion.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.NodalFiber
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (s a : R)
local notation "N" => Coordinate s

/-- The full smoothing node with the opposite tangent divisor removed. -/
abbrev TangentOpen := Localization.Away (q s + algebraMap R N a)

/-- The original first coordinate on the whole tangent open. -/
def tangentP : TangentOpen s a := algebraMap N _ (p s)

/-- The original second coordinate on the whole tangent open. -/
def tangentQ : TangentOpen s a := algebraMap N _ (q s)

/-- The original smoothing parameter is retained on the entire open. -/
theorem tangent_relation : tangentP s a * tangentQ s a = algebraMap R (TangentOpen s a) s := by
  rw [tangentP, tangentQ, ← map_mul, relation,
    ← IsScalarTower.algebraMap_apply R N _]

/-- The tangent denominator is a unit by the actual localization. -/
theorem tangent_denominator_isUnit :
    IsUnit (tangentQ s a + algebraMap R (TangentOpen s a) a) := by
  simpa only [tangentQ, map_add, ← IsScalarTower.algebraMap_apply R N _] using
    IsLocalization.Away.algebraMap_isUnit (S := TangentOpen s a)
      (q s + algebraMap R N a)

/-- The fractional branch coordinate is defined on the whole initial tangent open. -/
def tangentFraction : TangentOpen s a :=
  tangentQ s a * ↑((tangent_denominator_isUnit s a).unit⁻¹)

/-- Its denominator equation holds at the node as well as on its punctures. -/
theorem tangentFraction_denominator :
    tangentFraction s a * (tangentQ s a + algebraMap R (TangentOpen s a) a) =
      tangentQ s a := by
  rw [tangentFraction, mul_assoc, (tangent_denominator_isUnit s a).val_inv_mul,
    mul_one]

/-- The deleted value one differs by precisely the inverse tangent denominator. -/
theorem tangentFraction_sub_one :
    tangentFraction s a - 1 = -algebraMap R (TangentOpen s a) a *
      ↑((tangent_denominator_isUnit s a).unit⁻¹) := by
  have h := (tangent_denominator_isUnit s a).mul_val_inv
  dsimp only [tangentFraction]
  linear_combination h

/-- A unit tangent guarantees that the fractional coordinate avoids one everywhere. -/
theorem tangentFraction_sub_one_isUnit (ha : IsUnit a) :
    IsUnit (tangentFraction s a - 1) := by
  rw [tangentFraction_sub_one]
  exact (ha.map (algebraMap R (TangentOpen s a))).neg.mul (Units.isUnit _)

end FLT.Mazur.NodalFiber
