/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentNodePrincipalParts
public import FLT.Mazur.PolygonFirstNodePolynomialDescent
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Canonical representatives of the nilpotent node obstruction

The two Laurent principal parts detect descent of the entire parameter
layer. Subtracting them always gives an actual node function. Two weighted
pairs have the same class modulo node functions exactly when their canonical
principal parts agree, so this is a faithful concrete obstruction coordinate.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial LaurentNodePrincipalParts
variable (R : Type) [CommRing R]
local notation "S" => Ring R 1
local notation "L" => (S)[T;T⁻¹]

/-- Parameter weighting on both branches as an additive map. -/
def firstNodeParameterPair : (R[T;T⁻¹] × R[T;T⁻¹]) →+ ((L) × (L)) where
  toFun p := (firstLaurentParameterLift R p.1, firstLaurentParameterLift R p.2)
  map_zero' := Prod.ext (firstLaurentParameterLift_zero R) (firstLaurentParameterLift_zero R)
  map_add' p q := Prod.ext (firstLaurentParameterLift_add R p.1 q.1)
    (firstLaurentParameterLift_add R p.2 q.2)

/-- Weighting loses no reduced Laurent pair. -/
theorem firstNodeParameterPair_injective : Function.Injective (firstNodeParameterPair R) := by
  intro p q hpq
  exact Prod.ext (firstLaurentParameterLift_injective R (congrArg Prod.fst hpq))
    (firstLaurentParameterLift_injective R (congrArg Prod.snd hpq))

/-- The explicit principal parts detect descent of every nilpotent branch pair. -/
theorem firstNodeParameterPair_mem_iff (p : R[T;T⁻¹] × R[T;T⁻¹]) :
    firstNodeParameterPair R p ∈ firstNodeBranchSubalgebra R ↔ principalParts p = 0 := by
  rw [show firstNodeParameterPair R p =
    (firstLaurentParameterLift R p.1, firstLaurentParameterLift R p.2) from rfl,
    firstNodeBranchSubalgebra_parameter_polynomial_iff, principalParts_zero_iff]

/-- The discarded part is always an actual node function, with all nilpotents retained. -/
theorem firstNodeParameterPair_sub_principalParts (p : R[T;T⁻¹] × R[T;T⁻¹]) :
    firstNodeParameterPair R p - firstNodeParameterPair R (principalParts p) ∈
      firstNodeBranchSubalgebra R := by
  rw [← map_sub, firstNodeParameterPair_mem_iff, map_sub, principalParts_idempotent, sub_self]

/-- The additive class of a weighted pair modulo the unchanged full node subalgebra. -/
def firstNodeParameterClass : (R[T;T⁻¹] × R[T;T⁻¹]) →+
    (((L) × (L)) ⧸ (firstNodeBranchSubalgebra R).toSubmodule.toAddSubgroup) :=
  (QuotientAddGroup.mk' _).comp (firstNodeParameterPair R)

/-- A class vanishes exactly when its computed principal parts vanish. -/
theorem firstNodeParameterClass_zero_iff (p : R[T;T⁻¹] × R[T;T⁻¹]) :
    firstNodeParameterClass R p = 0 ↔ principalParts p = 0 := by
  change QuotientAddGroup.mk' _ (firstNodeParameterPair R p) = 0 ↔ _
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  exact firstNodeParameterPair_mem_iff R p

/-- Two parameter-layer classes coincide exactly when their canonical remainders coincide. -/
theorem firstNodeParameterClass_eq_iff (p q : R[T;T⁻¹] × R[T;T⁻¹]) :
    firstNodeParameterClass R p = firstNodeParameterClass R q ↔
      principalParts p = principalParts q := by
  rw [← sub_eq_zero, ← map_sub, firstNodeParameterClass_zero_iff, map_sub, sub_eq_zero]

/-- Passing to the canonical remainder preserves the full obstruction class. -/
theorem firstNodeParameterClass_principalParts (p : R[T;T⁻¹] × R[T;T⁻¹]) :
    firstNodeParameterClass R (principalParts p) = firstNodeParameterClass R p :=
  (firstNodeParameterClass_eq_iff R _ _).mpr (principalParts_idempotent p)

end FLT.Mazur.PolygonInfinitesimalStages
