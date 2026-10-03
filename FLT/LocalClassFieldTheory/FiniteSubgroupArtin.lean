/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteArtin
public import FLT.LocalClassFieldTheory.RelativeSubgroupCupIso

/-!
# The subgroup Artin map on fixed units

Invert the proved restricted-class cup on subgroup-invariant units. Coset
transfer into base-field units intertwines this map with the original finite
Artin map and the actual inclusion on abelianizations.
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

/-- The subgroup Artin map on the actual fixed-unit module. -/
def finiteSubgroupArtin : (MH).ρ.invariants →+ Additive (Abelianization H) :=
  (tateScalarAbelianizationEquiv H).toAddMonoidHom.comp
    ((relativeSubgroupCupEquiv R S K C F p H).symm.toAddMonoidHom.comp
      (tateInvariantClass MH).hom.toAddMonoidHom)

/-- The subgroup Artin map is surjective. -/
theorem finiteSubgroupArtin_surjective :
    Function.Surjective (finiteSubgroupArtin R S K C F p H) :=
  (tateScalarAbelianizationEquiv H).surjective.comp
    ((relativeSubgroupCupEquiv R S K C F p H).symm.surjective.comp
      (tateInvariantClass_surjective MH))

/-- The subgroup Artin kernel is exactly the subgroup norm image. -/
theorem finiteSubgroupArtin_eq_zero_iff (x : (MH).ρ.invariants) :
    finiteSubgroupArtin R S K C F p H x = 0 ↔
      ∃ y : MH, (MH).norm.hom y = (x : MH) := by
  change tateScalarAbelianizationEquiv H
    ((relativeSubgroupCupEquiv R S K C F p H).symm (tateInvariantClass MH x)) = 0 ↔ _
  rw [map_eq_zero_iff _ (tateScalarAbelianizationEquiv H).injective,
    map_eq_zero_iff _ (relativeSubgroupCupEquiv R S K C F p H).symm.injective,
    tateInvariantClass_eq_zero_iff]

variable [Fintype (Gal(F/K) ⧸ H)]

/-- The inverse subgroup and ambient cups intertwine coset transfer. -/
theorem relativeSubgroupCup_inverse_corestriction (x : tateCohomology MH 0) :
    (relativeFundamentalTateCupNegTwoEquiv R S K C F p).symm
      (tateZeroCorestriction M H x) =
        tateScalarMap H.subtype ((relativeSubgroupCupEquiv R S K C F p H).symm x) := by
  apply (relativeFundamentalTateCupNegTwoEquiv R S K C F p).injective
  rw [LinearEquiv.apply_symm_apply]
  have h := tateTwoClassMap_corestriction M H
    (relativeFundamentalOrdinaryClass R S K C F)
    ((relativeSubgroupCupEquiv R S K C F p H).symm x)
  change tateZeroCorestriction M H
    ((relativeSubgroupCupEquiv R S K C F p H)
      ((relativeSubgroupCupEquiv R S K C F p H).symm x)) = _ at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h

/-- The original finite Artin map intertwines subgroup transfer and Galois inclusion. -/
theorem finiteArtin_subgroup_transfer (x : (MH).ρ.invariants) :
    finiteArtin R S K C F p
      ((finiteUnitInvariantEquiv K F).symm (transferInvariant M H x)) =
        (Abelianization.map H.subtype).toAdditive
          (finiteSubgroupArtin R S K C F p H x) := by
  change tateScalarAbelianizationEquiv Gal(F/K)
    ((relativeFundamentalTateCupNegTwoEquiv R S K C F p).symm
      (tateInvariantClass M
        ((finiteUnitInvariantEquiv K F) ((finiteUnitInvariantEquiv K F).symm _)))) = _
  rw [LinearEquiv.apply_symm_apply, ← tateZeroCorestriction_class,
    relativeSubgroupCup_inverse_corestriction]
  change tateScalarAbelianizationEquiv Gal(F/K)
    ((tateScalarAbelianizationEquiv Gal(F/K)).symm _) = _
  exact AddEquiv.apply_symm_apply _ _

end LocalClassFieldTheory
