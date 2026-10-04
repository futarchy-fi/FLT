/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.SubgroupFixedFieldCup

/-!
# The subgroup Artin map agrees with the field-wise construction

Transport through the actual fixed-field Galois equivalence identifies the
inverse restricted cup with the independently constructed field-wise Artin map.
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

variable [IsLocalRing (integralClosure R (subgroupFixedField F H))]
  [Finite (ResidueField (integralClosure R (subgroupFixedField F H)))]
  [CharP (ResidueField (integralClosure R (subgroupFixedField F H))) p]

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

set_option maxHeartbeats 1600000 in
-- Comparing inverse cups unfolds the two concrete finite-field representations.
/-- The fixed-field Artin map equals the transported subgroup Artin map. -/
theorem finiteSubgroupArtin_fixedField (u : Additive Eˣ) :
    (Abelianization.map (e).toMonoidHom).toAdditive
      (finiteSubgroupArtin R S K C F p H
        (groupEquivalenceInvariant MF MH e (subgroupFixedFieldCoefficients K C F H)
          (finiteUnitInvariantInclusion E Fₕ u))) =
      finiteArtin T S E C Fₕ p u := by
  apply (tateScalarAbelianizationEquiv Gal(Fₕ/E)).symm.injective
  change tateScalarMap (e).toMonoidHom
    ((relativeSubgroupCupEquiv R S K C F p H).symm
      (tateInvariantClass MH _)) =
    (tateScalarAbelianizationEquiv Gal(Fₕ/E)).symm
      ((tateScalarAbelianizationEquiv Gal(Fₕ/E))
        ((relativeFundamentalTateCupNegTwoEquiv T S E C Fₕ p).symm
          (tateInvariantClass MF (finiteUnitInvariantInclusion E Fₕ u))))
  rw [AddEquiv.symm_apply_apply]
  apply (relativeFundamentalTateCupNegTwoEquiv T S E C Fₕ p).injective
  rw [LinearEquiv.apply_symm_apply]
  apply tateZeroGroupEquivalence_injective MF MH e
    (subgroupFixedFieldCoefficients K C F H) Function.bijective_id
  rw [subgroupFixedField_cup R S K C F p H, LinearEquiv.apply_symm_apply,
    tateZeroGroupEquivalence_class]

end LocalClassFieldTheory
