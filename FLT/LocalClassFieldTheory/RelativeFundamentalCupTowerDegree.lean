/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RelativeFundamentalOrdinaryInflation
public import FLT.LocalClassFieldTheory.FiniteTowerInflatedCup
public import FLT.LocalClassFieldTheory.TateZeroCardinality

/-!
# Degree-weighted fundamental-cup comparison in a tower

Arithmetic inflation and the explicit negative-cup formula prove the tower
square after multiplication by the relative degree. The remaining defect
is killed by the gcd of the two tower degrees, so coprime towers commute.
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
  relativeFundamentalInflationFiniteOverBase relativeFundamentalInflationTopAlgebra
  relativeFundamentalInflationTopFractionRing relativeFundamentalInflationTopTower
  relativeFundamentalInflationBaseTower relativeInflationGalois
  relativeInflationMiddleAlgebra relativeInflationMiddleTower

variable [TopologicalSpace (Additive Eˣ)] [DiscreteTopology (Additive Eˣ)]
  [TopologicalSpace (Additive Fˣ)] [DiscreteTopology (Additive Fˣ)]

attribute [local instance] relativeFundamentalInflationUnitTopology
  relativeFundamentalInflationUnitDiscrete

variable [CharZero C] (p : ℕ) [Fact p.Prime]
  [CharP (ResidueField R) p]

local notation "ME" => Rep.ofAlgebraAutOnUnits K E
local notation "MF" => Rep.ofAlgebraAutOnUnits K (F.restrictScalars K)
local notation "f" =>
  (AlgEquiv.restrictNormalHom E : Gal((F.restrictScalars K)/K) →* Gal(E/K))

include p in
/-- The negative fundamental-cup tower square commutes after the relative degree multiple. -/
theorem relativeFundamentalTateCup_tower_nsmul
    (x : tateCohomology (Rep.trivial ℤ Gal((F.restrictScalars K)/K) ℤ) (-2)) :
    Module.finrank E F • finiteTateNormTower K E (F.restrictScalars K)
      (relativeFundamentalTateCup R T K C (F.restrictScalars K) (-2) x) =
    Module.finrank E F • relativeFundamentalTateCup R S K C E (-2) (tateScalarMap f x) := by
  have h := finiteTateNormTower_inflated_class K E (F.restrictScalars K)
    (relativeFundamentalOrdinaryClass R S K C E) x
  have hc := relativeFundamentalOrdinaryClass_inflation R S T K C E F p
  change groupCohomology.map f (finiteTowerCoefficients K E (F.restrictScalars K)) 2
    (relativeFundamentalOrdinaryClass R S K C E) =
      Module.finrank E F • relativeFundamentalOrdinaryClass R T K C (F.restrictScalars K) at hc
  rw [hc, tateTwoClassMap_negTwo_nsmul, map_nsmul] at h
  exact h

include p in
/-- The residual tower defect is killed by the gcd of the two field degrees. -/
theorem relativeFundamentalTateCup_tower_gcd
    (x : tateCohomology (Rep.trivial ℤ Gal((F.restrictScalars K)/K) ℤ) (-2)) :
    Nat.gcd (Module.finrank E F) (Module.finrank K E) •
      (@Sub.sub (tateCohomology ME 0) _
        (finiteTateNormTower K E (F.restrictScalars K)
          (relativeFundamentalTateCup R T K C (F.restrictScalars K) (-2) x))
        (relativeFundamentalTateCup R S K C E (-2) (tateScalarMap f x))) = 0 := by
  let a : tateCohomology ME 0 := finiteTateNormTower K E (F.restrictScalars K)
    (relativeFundamentalTateCup R T K C (F.restrictScalars K) (-2) x)
  let b : tateCohomology ME 0 :=
    relativeFundamentalTateCup R S K C E (-2) (tateScalarMap f x)
  change Nat.gcd (Module.finrank E F) (Module.finrank K E) • (a - b) = 0
  have h : Module.finrank E F • a = Module.finrank E F • b :=
    relativeFundamentalTateCup_tower_nsmul R S T K C E F p x
  have hd : Module.finrank E F • (a - b) = 0 := by rw [smul_sub, h, sub_self]
  have hg := tateZero_gcd_nsmul ME (Module.finrank E F) (a - b) hd
  rwa [IsGalois.card_aut_eq_finrank] at hg

include p in
/-- Coprime tower degrees permit cancellation, giving the actual unweighted cup square. -/
theorem relativeFundamentalTateCup_tower_of_coprime
    (hcop : (Module.finrank E F).Coprime (Module.finrank K E))
    (x : tateCohomology (Rep.trivial ℤ Gal((F.restrictScalars K)/K) ℤ) (-2)) :
    finiteTateNormTower K E (F.restrictScalars K)
      (relativeFundamentalTateCup R T K C (F.restrictScalars K) (-2) x) =
      relativeFundamentalTateCup R S K C E (-2) (tateScalarMap f x) := by
  apply tateZero_nsmul_injective ME (Module.finrank E F)
    (by rwa [IsGalois.card_aut_eq_finrank])
  exact relativeFundamentalTateCup_tower_nsmul R S T K C E F p x

end LocalClassFieldTheory
