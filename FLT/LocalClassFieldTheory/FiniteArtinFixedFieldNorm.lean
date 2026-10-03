/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteSubgroupArtin
public import FLT.LocalClassFieldTheory.NormalFixedFieldNorm

/-!
# The finite Artin norm diagram for a normal subgroup

The algebraic fixed-field norm on units intertwines the original finite Artin
map with the constructed subgroup Artin map and the actual abelianized inclusion.
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

variable (H : Subgroup Gal(F/K)) [Fintype H]

local notation "MH" => Rep.res H.subtype M


variable [H.Normal]

/-- The Artin norm diagram for the actual algebraic norm of a normal fixed field. -/
theorem finiteArtin_fixedField_norm (v : (IntermediateField.fixedField H)ˣ) :
    finiteArtin R S K C F p (Additive.ofMul (Units.map (Algebra.norm K) v)) =
      (Abelianization.map H.subtype).toAdditive
        (finiteSubgroupArtin R S K C F p H
          (fixedUnitInvariantInclusion K F H (Additive.ofMul v))) := by
  classical
  let : Fintype (Gal(F/K) ⧸ H) := Fintype.ofFinite _
  have h := finiteArtin_subgroup_transfer R S K C F p H
    (fixedUnitInvariantInclusion K F H (Additive.ofMul v))
  rw [transferInvariant_fixedUnit_norm] at h
  change finiteArtin R S K C F p
    ((finiteUnitInvariantEquiv K F).symm
      ((finiteUnitInvariantEquiv K F) (Additive.ofMul (Units.map (Algebra.norm K) v)))) = _ at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact h

end LocalClassFieldTheory
