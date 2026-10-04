/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RelativeFundamentalCupTower
public import FLT.LocalClassFieldTheory.FiniteArtin

/-!
# The actual Artin tower identity for arbitrary relative degrees

Inverting the proved fundamental-cup comparison identifies the independently
constructed Artin maps. No comparison map or evaluation is supplied as data.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory

variable (R S T K C : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Algebra R T] [Module.Finite R T] [FaithfulSMul R T]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  (E : IntermediateField K C) (F : IntermediateField E C)
  [Algebra S E] [IsFractionRing S E] [Algebra S C] [IsScalarTower S E C]
  [IsScalarTower R S E] [IsScalarTower R S C]
  [Algebra T F] [IsFractionRing T F] [Algebra T C] [IsScalarTower T F C]
  [IsScalarTower R T C]
  [Algebra.IsSeparable K C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)] [Finite (ResidueField T)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]
  [IsAdicComplete (maximalIdeal T) T]
  [IsGalois K E] [IsGalois K (F.restrictScalars K)]
  [FiniteDimensional K E] [FiniteDimensional K (F.restrictScalars K)]

attribute [local instance] relativeBaseTower unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

attribute [local instance] relativeFundamentalInflationFinite
  relativeFundamentalInflationFiniteOverBase
  relativeFundamentalInflationTopFractionRing relativeFundamentalInflationTopTower
  relativeFundamentalInflationBaseTower relativeInflationGalois
  relativeInflationMiddleAlgebra relativeInflationMiddleTower

attribute [local instance 100] relativeFundamentalInflationTopAlgebra

variable [TopologicalSpace (Additive Eˣ)] [DiscreteTopology (Additive Eˣ)]
  [TopologicalSpace (Additive Fˣ)] [DiscreteTopology (Additive Fˣ)]

attribute [local instance] relativeFundamentalInflationUnitTopology
  relativeFundamentalInflationUnitDiscrete

variable [CharZero C] (p : ℕ) [Fact p.Prime]
  [CharP (ResidueField R) p] [CharP (ResidueField S) p] [CharP (ResidueField T) p]

local notation "ME" => Rep.ofAlgebraAutOnUnits K E
local notation "MF" => Rep.ofAlgebraAutOnUnits K (F.restrictScalars K)
local notation "f" =>
  (AlgEquiv.restrictNormalHom E : Gal((F.restrictScalars K)/K) →* Gal(E/K))

/-- Inverse fundamental cups commute with the tower projection in every finite tower. -/
theorem relativeFundamentalCup_inverse_tower
    (x : tateCohomology MF 0) :
    (relativeFundamentalTateCupNegTwoEquiv R S K C E p).symm
      (finiteTateNormTower K E (F.restrictScalars K) x) =
    tateScalarMap f
      ((relativeFundamentalTateCupNegTwoEquiv R T K C (F.restrictScalars K) p).symm x) := by
  apply (relativeFundamentalTateCupNegTwoEquiv R S K C E p).injective
  rw [LinearEquiv.apply_symm_apply]
  have h := relativeFundamentalTateCup_tower R S T K C E F p
    ((relativeFundamentalTateCupNegTwoEquiv R T K C (F.restrictScalars K) p).symm x)
  change finiteTateNormTower K E (F.restrictScalars K)
    ((relativeFundamentalTateCupNegTwoEquiv R T K C (F.restrictScalars K) p)
      ((relativeFundamentalTateCupNegTwoEquiv R T K C (F.restrictScalars K) p).symm x)) = _ at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h

set_option maxHeartbeats 600000 in
-- Comparing the two field presentations unfolds both constructed inverse cup equivalences.
/-- The actual finite Artin maps commute with Galois restriction in every finite tower. -/
theorem finiteArtin_tower
    (u : Additive Kˣ) :
    finiteArtin R S K C E p u =
      (Abelianization.map f).toAdditive (finiteArtin R T K C (F.restrictScalars K) p u) := by
  change tateScalarAbelianizationEquiv Gal(E/K)
    ((relativeFundamentalTateCupNegTwoEquiv R S K C E p).symm
      (tateInvariantClass ME (finiteUnitInvariantInclusion K E u))) = _
  rw [← finiteTateNormTower_unit K E (F.restrictScalars K),
    relativeFundamentalCup_inverse_tower R S T K C E F p]
  change tateScalarAbelianizationEquiv Gal(E/K)
    ((tateScalarAbelianizationEquiv Gal(E/K)).symm _) = _
  exact (tateScalarAbelianizationEquiv Gal(E/K)).apply_symm_apply _

end LocalClassFieldTheory
