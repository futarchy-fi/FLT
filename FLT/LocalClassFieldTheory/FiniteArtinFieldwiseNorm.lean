/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CanonicalFixedFieldArtin
public import FLT.LocalClassFieldTheory.FixedFieldCosetNorm
public import FLT.LocalClassFieldTheory.FixedFieldUnitInvariants

/-!
# The field-wise finite Artin norm diagram

The norm from any subgroup fixed field, including a nonnormal one, intertwines
the independently constructed finite Artin maps and restriction of scalars.
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

omit [IsGalois K F] [Algebra.IsSeparable K C] [IsSepClosed C]
  [TopologicalSpace (Additive Fˣ)] [DiscreteTopology (Additive Fˣ)]
  [CharZero C] [Fintype H] in
/-- Transporting a fixed-field unit gives the original subgroup-invariant unit. -/
theorem fixedFieldUnit_transport (v : (IntermediateField.fixedField H)ˣ) :
    groupEquivalenceInvariant MF MH e (subgroupFixedFieldCoefficients K C F H)
      (finiteUnitInvariantInclusion E Fₕ
        (Additive.ofMul (Units.map
          (IntermediateField.liftAlgEquiv (IntermediateField.fixedField H)).toMonoidHom v))) =
      fixedUnitInvariantInclusion K F H (Additive.ofMul v) := by
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Units.ext
  rfl

/-- The two Artin constructions agree on every fixed-unit invariant via the unit equivalence. -/
theorem finiteSubgroupArtin_fixedUnitEquiv (x : (MH).ρ.invariants) :
    finiteFixedFieldArtin R S K C F p H (Additive.ofMul (Units.map
      (IntermediateField.liftAlgEquiv (IntermediateField.fixedField H)).toMonoidHom
        (((fixedUnitInvariantEquiv K F H).symm x).toMul))) =
      (Abelianization.map (e).toMonoidHom).toAdditive
        (finiteSubgroupArtin R S K C F p H x) := by
  rw [finiteFixedFieldArtin_eq_subgroup, fixedFieldUnit_transport K C F H]
  change (Abelianization.map (e).toMonoidHom).toAdditive
    (finiteSubgroupArtin R S K C F p H
      ((fixedUnitInvariantEquiv K F H) ((fixedUnitInvariantEquiv K F H).symm x))) = _
  rw [LinearEquiv.apply_symm_apply]

set_option maxHeartbeats 800000 in
-- The two presentations of fixed-field units expand their concrete field towers.
omit [Fintype H] in
/-- The actual algebraic fixed-field norm intertwines the two field-wise Artin maps. -/
theorem finiteArtin_fixedField_fieldwise_norm (v : (IntermediateField.fixedField H)ˣ) :
    finiteArtin R S K C F p (Additive.ofMul (Units.map (Algebra.norm K) v)) =
      (Abelianization.map (H.subtype.comp (e).symm.toMonoidHom)).toAdditive
        (finiteFixedFieldArtin R S K C F p H (Additive.ofMul (Units.map
          (IntermediateField.liftAlgEquiv (IntermediateField.fixedField H)).toMonoidHom v))) := by
  classical
  let : Fintype H := Fintype.ofFinite _
  let : Fintype (Gal(F/K) ⧸ H) := Fintype.ofFinite _
  rw [finiteFixedFieldArtin_eq_subgroup, fixedFieldUnit_transport K C F H]
  have hc := congrArg (fun f => f.toAdditive
    (finiteSubgroupArtin R S K C F p H
      (fixedUnitInvariantInclusion K F H (Additive.ofMul v))))
    (Abelianization.map_comp (e).toMonoidHom (H.subtype.comp (e).symm.toMonoidHom))
  change (Abelianization.map (H.subtype.comp (e).symm.toMonoidHom)).toAdditive
    ((Abelianization.map (e).toMonoidHom).toAdditive _) = _ at hc
  have he : (H.subtype.comp (e).symm.toMonoidHom).comp (e).toMonoidHom = H.subtype := by
    ext h
    simp
  rw [he] at hc
  rw [hc]
  have ht := finiteArtin_subgroup_transfer R S K C F p H
    (fixedUnitInvariantInclusion K F H (Additive.ofMul v))
  rw [transferInvariant_fixedField_coset_norm] at ht
  change finiteArtin R S K C F p
    ((finiteUnitInvariantEquiv K F).symm ((finiteUnitInvariantEquiv K F) _)) = _ at ht
  rw [LinearEquiv.symm_apply_apply] at ht
  exact ht

end LocalClassFieldTheory
