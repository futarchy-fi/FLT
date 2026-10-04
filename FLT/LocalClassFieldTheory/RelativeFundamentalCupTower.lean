/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RelativeFundamentalClassQuotient

/-!
# Unrestricted fundamental-cup compatibility in finite towers

Injective inflation identifies the smaller-field fundamental class with the
class of the divided invariant sequences. Their computed negative boundary
then gives the tower square without any coprimality condition.
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

local notation "N" => MonoidHom.ker f
local notation "MQ" => Rep.quotientToInvariants MF N
local notation "e" => finiteTowerQuotientGroup K E (F.restrictScalars K)
local notation "φ" => finiteTowerQuotientCoefficients K E (F.restrictScalars K)

include p in
omit [CharP (ResidueField S) p] in
/-- The actual fundamental cups commute with the norm-tower projection in every finite tower. -/
theorem relativeFundamentalTateCup_tower
    (x : tateCohomology (Rep.trivial ℤ Gal((F.restrictScalars K)/K) ℤ) (-2)) :
    finiteTateNormTower K E (F.restrictScalars K)
      (relativeFundamentalTateCup R T K C (F.restrictScalars K) (-2) x) =
      relativeFundamentalTateCup R S K C E (-2) (tateScalarMap f x) := by
  classical
  let : Fintype N := Fintype.ofFinite N
  let : Fintype (Gal((F.restrictScalars K)/K) ⧸ N) := Fintype.ofFinite _
  apply finiteTowerQuotient_tate_injective K E (F.restrictScalars K)
  rw [finiteTowerQuotient_deflation]
  change _ = tateZeroGroupEquivalence ME MQ e φ
    (tateTwoClassMap ME (relativeFundamentalOrdinaryClass R S K C E) (-2)
      (tateScalarMap f x))
  rw [finiteTowerQuotient_cup,
    relativeFundamentalOrdinaryClass_quotient R S T K C E F p]
  exact (relativeFundamentalInvariantTwoClass_negativeCup_deflation
    R T K C (F.restrictScalars K) p N x).symm

end LocalClassFieldTheory
