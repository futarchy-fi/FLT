/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CorestrictionInvariant
public import FLT.LocalClassFieldTheory.AbsoluteFundamentalClass

/-!
# Fundamental classes under finite base extension

Actual restriction cancels the base-extension degree from the denominator.
Actual corestriction preserves the denominator. These identities follow from
the proved formulas for the absolute local invariant.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory

variable (R S K C : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  (E : IntermediateField K C)
  [Algebra S E] [IsFractionRing S E] [Algebra S C] [IsScalarTower S E C]
  [IsScalarTower R S C] [IsScalarTower R S E]
  [Algebra.IsSeparable K C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]

local notation "A" => maximalUnramified R K C
local notation "B" => maximalUnramified S E C

attribute [local instance] unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

attribute [local instance] relativeBaseTower

variable [FiniteDimensional K E] [CharZero C]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p] [CharP (ResidueField S) p]

/-- Restriction cancels the extension degree in a fundamental class denominator. -/
theorem absoluteFundamentalClass_restriction (n : ℕ) :
    (absoluteRestriction K C E 2).hom
      (absoluteFundamentalClass R K C p (Module.finrank K E * n)) =
        absoluteFundamentalClass S E C p n := by
  apply (absoluteInvariant S E C p).injective
  rw [absoluteInvariant_restriction R S K C E p,
    absoluteFundamentalClass_invariant, absoluteFundamentalClass_invariant,
    ← AddCircle.coe_nsmul, nsmul_eq_mul]
  congr 1
  have hd : (Module.finrank K E : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev, one_mul, ← mul_assoc]
  rw [mul_right_comm, mul_inv_cancel₀ hd, one_mul]

/-- Corestriction preserves the denominator of the normalized fundamental class. -/
theorem absoluteFundamentalClass_corestriction (n : ℕ) :
    absoluteCorestriction K C E (absoluteFundamentalClass S E C p n) =
      absoluteFundamentalClass R K C p n := by
  apply (absoluteInvariant R K C p).injective
  rw [absoluteInvariant_corestriction R S K C E p,
    absoluteFundamentalClass_invariant, absoluteFundamentalClass_invariant]

include S in
/-- The fundamental class of a finite extension vanishes after restriction to that extension. -/
theorem absoluteFundamentalClass_restriction_zero :
    (absoluteRestriction K C E 2).hom
      (absoluteFundamentalClass R K C p (Module.finrank K E)) = 0 := by
  rw [← mul_one (Module.finrank K E), absoluteFundamentalClass_restriction R S K C E p]
  apply (absoluteInvariant S E C p).injective
  rw [absoluteFundamentalClass_invariant, map_zero]
  simp

end LocalClassFieldTheory
