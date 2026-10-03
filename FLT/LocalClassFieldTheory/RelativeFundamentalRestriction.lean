/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RelativeRestrictionTower
public import FLT.LocalClassFieldTheory.FundamentalClassBaseChange
public import FLT.LocalClassFieldTheory.FundamentalClasses

/-!
# Restriction of the finite relative fundamental class

The class for F/K restricts to the class for F/E. Injective inflation and
the absolute invariant prove the identity for the actual cohomology map.
No normality of E/K is required.
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
  [Algebra S T] [Module.Finite S T] [FaithfulSMul S T]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  (E : IntermediateField K C) (F : IntermediateField E C)
  [Algebra S E] [IsFractionRing S E] [Algebra S C] [IsScalarTower S E C]
  [IsScalarTower R S E] [IsScalarTower R S C]
  [Algebra T F] [IsFractionRing T F] [Algebra T C] [IsScalarTower T F C]
  [IsScalarTower R T C] [IsScalarTower S T C]
  [Algebra.IsSeparable K C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)] [Finite (ResidueField T)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]
  [IsAdicComplete (maximalIdeal T) T]
  [IsGalois K (F.restrictScalars K)] [IsGalois E F]
  [FiniteDimensional K E] [FiniteDimensional K (F.restrictScalars K)]

attribute [local instance] relativeBaseTower unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

/-- The canonical tower instance with the intermediate-field presentation made explicit. -/
local instance relativeFundamentalRestrictionFinite : FiniteDimensional K F :=
  inferInstanceAs (FiniteDimensional K (F.restrictScalars K))
/-- The canonical tower instance with the intermediate-field presentation made explicit. -/
local instance relativeFundamentalRestrictionFiniteOverBase : FiniteDimensional E F :=
  FiniteDimensional.right K E F
/-- The canonical tower instance with the intermediate-field presentation made explicit. -/
local instance relativeFundamentalRestrictionTopAlgebra : Algebra T (F.restrictScalars K) :=
  inferInstanceAs (Algebra T F)
/-- The canonical tower instance with the intermediate-field presentation made explicit. -/
local instance relativeFundamentalRestrictionTopFractionRing :
    IsFractionRing T (F.restrictScalars K) :=
  inferInstanceAs (IsFractionRing T F)
/-- The canonical tower instance with the intermediate-field presentation made explicit. -/
local instance relativeFundamentalRestrictionTopTower : IsScalarTower T (F.restrictScalars K) C :=
  inferInstanceAs (IsScalarTower T F C)
/-- The canonical tower instance with the intermediate-field presentation made explicit. -/
local instance relativeFundamentalRestrictionBaseTower : IsScalarTower R T (F.restrictScalars K) :=
  IsScalarTower.of_algebraMap_eq fun r => by
    apply (algebraMap (F.restrictScalars K) C).injective
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
/-- The canonical tower instance with the intermediate-field presentation made explicit. -/
local instance relativeFundamentalRestrictionMiddleTower : IsScalarTower S T F :=
  IsScalarTower.of_algebraMap_eq fun s => by
    apply (algebraMap F C).injective
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]

variable [TopologicalSpace (Additive Fˣ)] [DiscreteTopology (Additive Fˣ)]

/-- The canonical tower instance with the intermediate-field presentation made explicit. -/
local instance relativeFundamentalRestrictionUnitTopology :
    TopologicalSpace (Additive (F.restrictScalars K)ˣ) :=
  inferInstanceAs (TopologicalSpace (Additive Fˣ))
/-- The canonical tower instance with the intermediate-field presentation made explicit. -/
local instance relativeFundamentalRestrictionUnitDiscrete :
    DiscreteTopology (Additive (F.restrictScalars K)ˣ) :=
  inferInstanceAs (DiscreteTopology (Additive Fˣ))

variable [CharZero C] (p : ℕ) [Fact p.Prime]
  [CharP (ResidueField R) p] [CharP (ResidueField S) p]

include p in
/-- Restriction sends the positive relative fundamental class to the one over the new base. -/
theorem relativeFundamentalClass_restriction :
    (relativeRestriction K C E F 2).hom
      (relativeFundamentalClass R T K C (F.restrictScalars K)) =
        relativeFundamentalClass S T E C F := by
  apply galoisMultiplicativeInflationH2_injective E C F
  rw [relativeFundamentalClass_inflation S T E C F p]
  change (relativeRestriction K C E F 2 ≫ galoisMultiplicativeInflation E C F 2).hom
    (relativeFundamentalClass R T K C (F.restrictScalars K)) = _
  rw [relativeRestriction_inflation]
  change (absoluteRestriction K C E 2).hom
    ((galoisMultiplicativeInflation K C (F.restrictScalars K) 2).hom
      (relativeFundamentalClass R T K C (F.restrictScalars K))) = _
  rw [relativeFundamentalClass_inflation R T K C (F.restrictScalars K) p]
  have hd : Module.finrank K (F.restrictScalars K) =
      Module.finrank K E * Module.finrank E F := (Module.finrank_mul_finrank K E F).symm
  rw [hd, absoluteFundamentalClass_restriction R S K C E p]

end LocalClassFieldTheory
