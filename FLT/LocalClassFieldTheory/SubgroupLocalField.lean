/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteSubfieldDvr
public import FLT.LocalClassFieldTheory.SubgroupFixedFieldTower
public import FLT.LocalClassFieldTheory.UnramifiedBaseChangeInflationSquare

/-!
# Canonical local structures for a subgroup fixed field

The fixed field and its canonical integers form the local tower used to
compare field-wise and subgroup Artin maps. All structures are constructed.
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

attribute [local instance] relativeBaseTower

variable [TopologicalSpace (Additive Fˣ)] [DiscreteTopology (Additive Fˣ)]
  [CharZero C] (p : ℕ) [Fact p.Prime]
  [CharP (ResidueField R) p] [CharP (ResidueField S) p]

variable (H : Subgroup Gal(F/K))

local notation "E" => subgroupFixedField F H
local notation "Fₕ" => subgroupTopField F H
local notation "T" => integralClosure R E


/-- The canonical fixed-field tower structure. -/
local instance subgroupLocalFieldAlgebra : Algebra E F := inferInstanceAs (Algebra E Fₕ)

/-- The canonical fixed-field tower structure. -/
local instance subgroupLocalFieldTower :
    IsScalarTower K E F := inferInstanceAs (IsScalarTower K E Fₕ)

/-- The canonical fixed-field tower structure. -/
local instance subgroupLocalAmbientTower :
    IsScalarTower E F C := inferInstanceAs (IsScalarTower E Fₕ C)

/-- The canonical fixed-field tower structure. -/
local instance subgroupLocalBaseFinite : FiniteDimensional K E := FiniteDimensional.of_injective
    (IntermediateField.inclusion (subgroupFixedField_le F H)).toLinearMap
    (IntermediateField.inclusion_injective (subgroupFixedField_le F H))

/-- The canonical fixed-field tower structure. -/
local instance subgroupLocalRingFieldTower :
    IsScalarTower R E F := IsScalarTower.of_algebraMap_eq fun r => by
    apply (algebraMap F C).injective
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]

/-- The canonical fixed-field tower structure. -/
local instance subgroupLocalTopGalois : IsGalois K Fₕ := inferInstanceAs (IsGalois K F)

/-- The canonical fixed-field tower structure. -/
local instance subgroupLocalTopFinite :
    FiniteDimensional K Fₕ := inferInstanceAs (FiniteDimensional K F)

/-- The canonical fixed-field tower structure. -/
local instance subgroupLocalRelativeFinite :
    FiniteDimensional E Fₕ := FiniteDimensional.right K E Fₕ

/-- The canonical fixed-field tower structure. -/
local instance subgroupLocalTopAlgebra : Algebra S Fₕ := inferInstanceAs (Algebra S F)

/-- The canonical fixed-field tower structure. -/
local instance subgroupLocalTopFraction :
    IsFractionRing S Fₕ := inferInstanceAs (IsFractionRing S F)

/-- The canonical fixed-field tower structure. -/
local instance subgroupLocalTopAmbient :
    IsScalarTower S Fₕ C := inferInstanceAs (IsScalarTower S F C)

/-- The canonical fixed-field tower structure. -/
local instance subgroupLocalUnitTopology :
    TopologicalSpace (Additive Fₕˣ) := inferInstanceAs (TopologicalSpace (Additive Fˣ))

/-- The canonical fixed-field tower structure. -/
local instance subgroupLocalUnitDiscrete :
    DiscreteTopology (Additive Fₕˣ) := inferInstanceAs (DiscreteTopology (Additive Fˣ))

/-- The canonical fixed-field tower structure. -/
local instance subgroupLocalRelativeGalois : IsGalois E Fₕ := IsGalois.tower_top_of_isGalois K E Fₕ

/-- The canonical fixed-field tower structure. -/
local instance subgroupLocalDvrAlgebra : Algebra T S := finiteSubfieldDvrAlgebra R S E F

/-- The canonical fixed-field tower structure. -/
local instance subgroupLocalDvrBaseTower :
    IsScalarTower R T S := finiteSubfieldDvr_baseTower R S E F

/-- The canonical fixed-field tower structure. -/
local instance subgroupLocalDvrFieldTower :
    IsScalarTower T S F := finiteSubfieldDvr_fieldTower R S E F

/-- The canonical fixed-field tower structure. -/
local instance subgroupLocalDvrTopFinite : Module.Finite T S := finiteSubfieldDvr_topFinite R S E

/-- The canonical fixed-field tower structure. -/
local instance subgroupLocalDvrFaithful : FaithfulSMul T S := finiteSubfieldDvr_faithful R S E F

omit [IsDomain R] [IsDiscreteValuationRing R] [FaithfulSMul R S]
  [IsFractionRing R K] [IsGalois K F] [FiniteDimensional K F]
  [Algebra S C] [IsScalarTower S F C] [IsScalarTower R S C]
  [Algebra.IsSeparable K C] [IsSepClosed C] [Finite (ResidueField R)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]
  [TopologicalSpace (Additive Fˣ)] [DiscreteTopology (Additive Fˣ)] [CharZero C]
  [Finite (ResidueField S)] in
include S in
/-- The canonical fixed-field tower structure. -/
theorem subgroupLocalDvrLocal : IsLocalRing T := finiteSubfieldDvr_local R S E

variable [IsLocalRing (integralClosure R (subgroupFixedField F H))]

/-- The canonical fixed-field tower structure. -/
local instance subgroupLocalDvrDiscrete :
    IsDiscreteValuationRing T := finiteSubfieldDvr_discrete R K E

/-- The canonical fixed-field tower structure. -/
local instance subgroupLocalDvrFinite : Module.Finite R T := finiteSubfieldDvr_finite R K E

/-- The canonical fixed-field tower structure. -/
local instance subgroupLocalDvrFraction : IsFractionRing T E := finiteSubfieldDvr_fractionRing R K E

/-- The canonical fixed-field tower structure. -/
local instance subgroupLocalDvrBaseFaithful :
    FaithfulSMul R T := intermediateDvrBaseFaithful R K C E

omit [IsDomain R] [IsDiscreteValuationRing R] [FaithfulSMul R S]
  [IsFractionRing R K] [IsGalois K F] [FiniteDimensional K F]
  [Algebra S C] [IsScalarTower S F C] [IsScalarTower R S C]
  [Algebra.IsSeparable K C] [IsSepClosed C] [Finite (ResidueField R)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]
  [TopologicalSpace (Additive Fˣ)] [DiscreteTopology (Additive Fˣ)] [CharZero C] in
include S in
/-- The canonical fixed-field tower structure. -/
theorem subgroupLocalDvrResidueFinite :
    Finite (ResidueField T) := finiteSubfieldDvr_residueFinite R S E

omit [IsDomain R] [IsDiscreteValuationRing R] [FaithfulSMul R S]
  [IsFractionRing R K] [IsGalois K F] [FiniteDimensional K F]
  [Algebra S C] [IsScalarTower S F C] [IsScalarTower R S C]
  [Algebra.IsSeparable K C] [IsSepClosed C] [Finite (ResidueField R)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]
  [TopologicalSpace (Additive Fˣ)] [DiscreteTopology (Additive Fˣ)] [CharZero C]
  [Finite (ResidueField S)] [Fact p.Prime] [CharP (ResidueField R) p] in
include S in
/-- The canonical fixed-field tower structure. -/
theorem subgroupLocalDvrResidueChar :
    CharP (ResidueField T) p := finiteSubfieldDvr_residueChar R S E p

/-- The canonical fixed-field tower structure. -/
local instance subgroupLocalDvrComplete :
    IsAdicComplete (maximalIdeal T) T := finiteSubfieldDvr_complete R K E

/-- The canonical fixed-field tower structure. -/
local instance subgroupLocalDvrAmbientTower :
    IsScalarTower T S C := IsScalarTower.of_algebraMap_eq fun t => by
    change (algebraMap F C) ((algebraMap T F) t) = _
    rw [IsScalarTower.algebraMap_apply T S F, ← IsScalarTower.algebraMap_apply S F C]

/-- The canonical fixed-field tower structure. -/
local instance subgroupLocalRestrictGalois :
    IsGalois K ((Fₕ).restrictScalars K) := inferInstanceAs (IsGalois K F)

/-- The canonical fixed-field tower structure. -/
local instance subgroupLocalRestrictFinite : FiniteDimensional K ((Fₕ).restrictScalars K) :=
    inferInstanceAs (FiniteDimensional K F)

end LocalClassFieldTheory
