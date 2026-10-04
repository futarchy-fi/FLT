/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedCarryAbsoluteNormalization
public import FLT.LocalClassFieldTheory.RelativeFundamentalTateCup

/-!
# The finite uniformizer carry is the relative fundamental class

Injective absolute inflation identifies the explicit positive carry with the
independently constructed relative class. Its negative Tate sign is retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory groupCohomology

variable (R S K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]
  {π : R} (hπ : Irreducible π) (n : UnramifiedIndex)

local notation "U" => maximalUnramified R K C
local notation "E" => unramifiedStage R K C n.degree
local notation "F" => unramifiedFiniteStage R K C n

attribute [local instance] relativeBaseTower
  unramifiedOriginalCarryFinite unramifiedOriginalCarryGalois
  unramifiedOriginalCarryTopology unramifiedOriginalCarryDiscrete
  unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete
  trivialCoefficientAction trivialCoefficientIntComm trivialCoefficientContinuous

local notation "M" => Rep.ofAlgebraAutOnUnits K E
local notation "e" => unramifiedOriginalCarryCoordinate R K C n
local notation "x" => finiteUnitInvariantInclusion K E (Additive.ofMul (fractionUniformizer R K hπ))

variable [Algebra S (unramifiedStage R K C n.degree)]
  [IsFractionRing S (unramifiedStage R K C n.degree)] [Algebra S C]
  [IsScalarTower S (unramifiedStage R K C n.degree) C]
  [IsScalarTower R S (unramifiedStage R K C n.degree)] [IsScalarTower R S C]
  [Finite (ResidueField S)] [IsAdicComplete (maximalIdeal S) S]
  [CharZero C] (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]

include p

/-- The finite positive carry is the independently constructed relative fundamental class. -/
theorem unramifiedCarry_relativeFundamentalClass :
    unramifiedOriginalContinuousCarry R K C hπ n = relativeFundamentalClass R S K C E := by
  apply galoisMultiplicativeInflationH2_injective K C E
  rw [unramifiedOriginalCarry_absolute_fundamental R K C hπ n p,
    relativeFundamentalClass_inflation R S K C E p, finrank_unramifiedStage]

/-- The same identification holds in ordinary cohomology, the input to the Tate cup. -/
theorem unramifiedCarry_relativeFundamentalOrdinaryClass :
    H2π M (unramifiedOriginalOrdinaryCarry R K C hπ n) =
      relativeFundamentalOrdinaryClass R S K C E := by
  rw [← unramifiedOriginalContinuousCarry_ordinary,
    unramifiedCarry_relativeFundamentalClass R S K C hπ n p]
  rfl

/-- The relative fundamental cup is computed by the explicit uniformizer carry. -/
theorem unramifiedCarry_relativeFundamentalTateCup (i : ℤ) :
    relativeFundamentalTateCup R S K C E i =
      tateTwoExtensionMap M (unramifiedOriginalOrdinaryCarry R K C hπ n) i :=
  relativeFundamentalTateCup_representative R S K C E _
    (unramifiedCarry_relativeFundamentalOrdinaryClass R S K C hπ n p) i

end LocalClassFieldTheory
