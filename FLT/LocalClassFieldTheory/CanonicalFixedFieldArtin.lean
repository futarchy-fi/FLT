/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.SubgroupFixedFieldArtin

/-!
# The canonical Artin map over a subgroup fixed field

The complete integer DVR, finite residue field and residue characteristic
are constructed internally. The field-wise Artin map is identified with the
subgroup Artin map without any comparison or local-structure hypothesis.
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

variable (H : Subgroup Gal(F/K)) [Fintype H]

local notation "E" => subgroupFixedField F H
local notation "Fₕ" => subgroupTopField F H
local notation "T" => integralClosure R E

attribute [local instance]
  subgroupLocalFieldAlgebra
  subgroupLocalFieldTower
  subgroupLocalAmbientTower
  subgroupLocalBaseFinite
  subgroupLocalRingFieldTower
  subgroupLocalTopGalois
  subgroupLocalTopFinite
  subgroupLocalRelativeFinite
  subgroupLocalTopAlgebra
  subgroupLocalTopFraction
  subgroupLocalTopAmbient
  subgroupLocalUnitTopology
  subgroupLocalUnitDiscrete
  subgroupLocalRelativeGalois
  subgroupLocalDvrAlgebra
  subgroupLocalDvrBaseTower
  subgroupLocalDvrFieldTower
  subgroupLocalDvrTopFinite
  subgroupLocalDvrFaithful
  subgroupLocalDvrDiscrete
  subgroupLocalDvrFinite
  subgroupLocalDvrFraction
  subgroupLocalDvrBaseFaithful
  subgroupLocalDvrComplete
  subgroupLocalDvrAmbientTower
  subgroupLocalRestrictGalois
  subgroupLocalRestrictFinite subgroupFixedField_dvrTower

local notation "M" => Rep.ofAlgebraAutOnUnits K F
local notation "MH" => Rep.res H.subtype M
local notation "MF" => Rep.ofAlgebraAutOnUnits E Fₕ
local notation "e" => subgroupFixedFieldEquiv F H

/-- The separately constructed field-wise Artin map over the canonical fixed-field DVR. -/
def finiteFixedFieldArtin : Additive Eˣ →+ Additive (Abelianization Gal(Fₕ/E)) := by
  letI := subgroupLocalDvrLocal R S K C F H
  letI := subgroupLocalDvrResidueFinite R S K C F H
  letI := subgroupLocalDvrResidueChar R S K C F p H
  exact finiteArtin T S E C Fₕ p

/-- Canonical field-wise Artin transport through the actual fixed-field Galois equivalence. -/
theorem finiteFixedFieldArtin_eq_subgroup (u : Additive Eˣ) :
    finiteFixedFieldArtin R S K C F p H u =
      (Abelianization.map (e).toMonoidHom).toAdditive
        (finiteSubgroupArtin R S K C F p H
          (groupEquivalenceInvariant MF MH e (subgroupFixedFieldCoefficients K C F H)
            (finiteUnitInvariantInclusion E Fₕ u))) := by
  let := subgroupLocalDvrLocal R S K C F H
  let := subgroupLocalDvrResidueFinite R S K C F H
  let := subgroupLocalDvrResidueChar R S K C F p H
  exact (finiteSubgroupArtin_fixedField R S K C F p H u).symm

end LocalClassFieldTheory
