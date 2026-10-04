/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RelativeInvariantClassInflation
public import FLT.LocalClassFieldTheory.QuotientInflationInjective

/-!
# Uniqueness of the quotient fundamental class

Subgroup H¹ vanishing proves that quotient inflation is injective. Hence
the invariant two-class is uniquely determined by its proved normalization.
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
  (F : IntermediateField K C) [IsGalois K F] [FiniteDimensional K F]
  [Algebra S F] [IsFractionRing S F] [Algebra S C] [IsScalarTower S F C]
  [IsScalarTower R S F] [IsScalarTower R S C]
  [Algebra.IsSeparable K C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]

attribute [local instance] relativeBaseTower unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

variable [TopologicalSpace (Additive Fˣ)] [DiscreteTopology (Additive Fˣ)]
  [CharZero C] (p : ℕ) [Fact p.Prime]
  [CharP (ResidueField R) p] [CharP (ResidueField S) p]

local notation "M" => Rep.ofAlgebraAutOnUnits K F
local notation "c" => twoClassRepresentative M (relativeFundamentalOrdinaryClass R S K C F)
local notation "Q" => shiftedCoefficients M
local notation "b" => shiftedTwoCocycle M c

variable (N : Subgroup Gal(F/K)) [N.Normal] [Fintype N]


include R S p in
omit [Fintype N] in
/-- Arithmetic subgroup H¹ vanishing makes ordinary quotient inflation injective. -/
theorem relativeQuotientInflationH2_injective :
    Function.Injective (groupCohomology.map (QuotientGroup.mk' N)
      (quotientInflationCoefficients M N) 2) := by
  classical
  let : Fintype N := Fintype.ofFinite N
  have hi := relativeSubgroupCup_isIso R S K C F p N (-1)
  have hz : Limits.IsZero (tateCohomology (Rep.res N.subtype M) 1) :=
    (tateScalar_neg_one_isZero N).of_iso
      (asIso (relativeSubgroupCup R S K C F N (-1))).symm
  exact quotientInflationH2_injective M N
    (hz.of_iso ((TateCohomology.isoGroupCohomology 1).app (Rep.res N.subtype M)).symm)

/-- The divided invariant class is the unique class with its arithmetic inflation. -/
theorem relativeFundamentalInvariantTwoClass_unique
    (a : groupCohomology (Rep.quotientToInvariants M N) 2)
    (ha : groupCohomology.map (QuotientGroup.mk' N) (quotientInflationCoefficients M N) 2 a =
      Fintype.card N • relativeFundamentalOrdinaryClass R S K C F) :
    a = relativeFundamentalInvariantTwoClass R S K C F p N := by
  apply relativeQuotientInflationH2_injective R S K C F p N
  exact ha.trans (relativeFundamentalInvariantTwoClass_inflation R S K C F p N).symm

end LocalClassFieldTheory
