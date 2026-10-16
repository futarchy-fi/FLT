/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberAlgebra
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Fractional coordinates on the full zero-node tangent open

On D(q+a), the coordinate q/(q+a) sends the deleted opposite tangent to
infinity. Its difference from one is a unit when a is a unit. This is the
fractional coordinate needed to turn opposite initial reflection into inversion.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.NodalFiber
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (a : R)
local notation "N" => Coordinate (0 : R)

/-- The full zero node with the opposite tangent divisor removed. -/
abbrev ZeroTangentOpen := Localization.Away (q (0 : R) + algebraMap R N a)

/-- The original first coordinate on the whole tangent open. -/
def zeroTangentP : ZeroTangentOpen a := algebraMap N _ (p 0)

/-- The original second coordinate on the whole tangent open. -/
def zeroTangentQ : ZeroTangentOpen a := algebraMap N _ (q 0)

/-- Both components of the zero node remain present. -/
theorem zeroTangent_relation : zeroTangentP a * zeroTangentQ a = 0 := by
  rw [zeroTangentP, zeroTangentQ, ← map_mul, relation, map_zero, map_zero]

/-- The tangent denominator is a unit by the actual localization. -/
theorem zeroTangent_denominator_isUnit :
    IsUnit (zeroTangentQ a + algebraMap R (ZeroTangentOpen a) a) := by
  simpa only [zeroTangentQ, map_add, ← IsScalarTower.algebraMap_apply R N _] using
    IsLocalization.Away.algebraMap_isUnit (S := ZeroTangentOpen a)
      (q (0 : R) + algebraMap R N a)

/-- The fractional branch coordinate is defined on the whole initial tangent open. -/
def zeroTangentFraction : ZeroTangentOpen a :=
  zeroTangentQ a * ↑((zeroTangent_denominator_isUnit a).unit⁻¹)

/-- Its denominator equation holds at the node as well as on its punctures. -/
theorem zeroTangentFraction_denominator :
    zeroTangentFraction a * (zeroTangentQ a + algebraMap R (ZeroTangentOpen a) a) =
      zeroTangentQ a := by
  rw [zeroTangentFraction, mul_assoc, (zeroTangent_denominator_isUnit a).val_inv_mul,
    mul_one]

/-- The fractional branch coordinate still has zero product with the first branch. -/
theorem zeroTangentFraction_relation : zeroTangentP a * zeroTangentFraction a = 0 := by
  rw [zeroTangentFraction, ← mul_assoc, zeroTangent_relation, zero_mul]

/-- The deleted value one differs by precisely the inverse tangent denominator. -/
theorem zeroTangentFraction_sub_one :
    zeroTangentFraction a - 1 = -algebraMap R (ZeroTangentOpen a) a *
      ↑((zeroTangent_denominator_isUnit a).unit⁻¹) := by
  have h := (zeroTangent_denominator_isUnit a).mul_val_inv
  dsimp only [zeroTangentFraction]
  linear_combination h

/-- A unit tangent guarantees that the fractional coordinate avoids one everywhere. -/
theorem zeroTangentFraction_sub_one_isUnit (ha : IsUnit a) :
    IsUnit (zeroTangentFraction a - 1) := by
  rw [zeroTangentFraction_sub_one]
  exact (ha.map (algebraMap R (ZeroTangentOpen a))).neg.mul (Units.isUnit _)

end FLT.Mazur.NodalFiber
