/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteSubgroupArtin
public import FLT.LocalClassFieldTheory.FixedFieldCosetNorm
public import FLT.LocalClassFieldTheory.FixedFieldUnitInvariants

/-!
# The Artin image of a fixed-field norm

For every subgroup, the fixed-field norm maps onto the image of the subgroup
in the ambient abelianization. Both Artin maps and the field norm are the
constructed maps.
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


local notation "E" => IntermediateField.fixedField H

/-- The subgroup norm diagram for an arbitrary, possibly nonnormal, fixed field. -/
theorem finiteArtin_arbitraryFixedField_norm (v : Eˣ) :
    finiteArtin R S K C F p (Additive.ofMul (Units.map (Algebra.norm K) v)) =
      (Abelianization.map H.subtype).toAdditive
        (finiteSubgroupArtin R S K C F p H
          (fixedUnitInvariantInclusion K F H (Additive.ofMul v))) := by
  classical
  let : Fintype (Gal(F/K) ⧸ H) := Fintype.ofFinite _
  have ht := finiteArtin_subgroup_transfer R S K C F p H
    (fixedUnitInvariantInclusion K F H (Additive.ofMul v))
  rw [transferInvariant_fixedField_coset_norm] at ht
  change finiteArtin R S K C F p
    ((finiteUnitInvariantEquiv K F).symm ((finiteUnitInvariantEquiv K F) _)) = _ at ht
  rw [LinearEquiv.symm_apply_apply] at ht
  exact ht

omit [Fintype H] in
/-- Fixed-field norms have exactly the subgroup's image in the ambient abelianization. -/
theorem finiteArtin_fixedField_norm_image (a : Additive (Abelianization Gal(F/K))) :
    (∃ v : Eˣ, finiteArtin R S K C F p
      (Additive.ofMul (Units.map (Algebra.norm K) v)) = a) ↔
    ∃ b : Additive (Abelianization H), (Abelianization.map H.subtype).toAdditive b = a := by
  classical
  let : Fintype H := Fintype.ofFinite _
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨finiteSubgroupArtin R S K C F p H
      (fixedUnitInvariantInclusion K F H (Additive.ofMul v)),
      (finiteArtin_arbitraryFixedField_norm R S K C F p H v).symm.trans hv⟩
  · rintro ⟨b, hb⟩
    obtain ⟨x, hx⟩ := finiteSubgroupArtin_surjective R S K C F p H b
    obtain ⟨v, rfl⟩ := fixedUnitInvariantInclusion_surjective K F H x
    refine ⟨v.toMul, ?_⟩
    rw [finiteArtin_arbitraryFixedField_norm]
    exact (congrArg (Abelianization.map H.subtype).toAdditive hx).trans hb

end LocalClassFieldTheory
