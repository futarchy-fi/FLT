/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RelativeFundamentalInflation
public import FLT.LocalClassFieldTheory.RelativeFundamentalTateCup
public import FLT.LocalClassFieldTheory.FiniteRestrictionComparison

/-!
# Ordinary inflation of the relative fundamental class

The continuous arithmetic inflation identity transports to the ordinary
finite-group two-class used to construct the negative Tate cup.
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

variable [TopologicalSpace (Additive Eˣ)] [DiscreteTopology (Additive Eˣ)]
  [TopologicalSpace (Additive Fˣ)] [DiscreteTopology (Additive Fˣ)]

attribute [local instance] relativeFundamentalInflationUnitTopology
  relativeFundamentalInflationUnitDiscrete

variable [CharZero C] (p : ℕ) [Fact p.Prime]
  [CharP (ResidueField R) p]

include p in
/-- Inflation of the ordinary fundamental two-class has the actual top-field degree factor. -/
theorem relativeFundamentalOrdinaryClass_inflation :
    groupCohomology.map (AlgEquiv.restrictNormalHom E : Gal(F/K) →* Gal(E/K))
        (relativeInflationCoefficients K C E F) 2
        (relativeFundamentalOrdinaryClass R S K C E) =
      Module.finrank E F • relativeFundamentalOrdinaryClass R T K C (F.restrictScalars K) := by
  have h := finiteContinuousCohomologyIso_restriction
    (AlgEquiv.restrictNormalHom E : Gal(F/K) →* Gal(E/K))
    continuous_of_discreteTopology (relativeInflationCoefficients K C E F) 2
  have he := congrArg (fun u => u.hom (relativeFundamentalClass R S K C E)) h
  change (finiteContinuousCohomologyIso ℤ Gal(F/K) (Additive Fˣ) 2).hom
    ((relativeInflation K C E F 2).hom (relativeFundamentalClass R S K C E)) = _ at he
  rw [relativeFundamentalClass_tower R S T K C E F p, map_nsmul] at he
  exact he.symm

end LocalClassFieldTheory
