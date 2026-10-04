/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.SubgroupLocalField
public import FLT.LocalClassFieldTheory.FiniteSubgroupArtin
public import FLT.LocalClassFieldTheory.RelativeFundamentalOrdinaryRestriction
public import FLT.LocalClassFieldTheory.TwoExtensionGroupEquivalence

/-!
# The fundamental class over a subgroup fixed field

The actual field-wise fundamental class transports to the restricted ambient
class through the fixed-field Galois equivalence and the identity on units.
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
  subgroupLocalRestrictFinite

local notation "M" => Rep.ofAlgebraAutOnUnits K F
local notation "MH" => Rep.res H.subtype M
local notation "MF" => Rep.ofAlgebraAutOnUnits E Fₕ
local notation "e" => subgroupFixedFieldEquiv F H

/-- The integer tower in the fixed-field presentation of the top field. -/
local instance subgroupFixedField_dvrTower : IsScalarTower T S Fₕ :=
  inferInstanceAs (IsScalarTower T S F)

/-- The identity on units along the fixed-field Galois equivalence. -/
def subgroupFixedFieldCoefficients : Rep.res (e).toMonoidHom MF ⟶ MH :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

set_option maxHeartbeats 1600000 in
-- Coefficient transport compares the concrete restricted representation actions.
omit [Fintype H] [CharP (ResidueField S) p] in
include p in
/-- The field-wise fundamental class becomes the restricted ambient class. -/
theorem subgroupFixedField_fundamentalClass :
    groupCohomology.map (e).toMonoidHom (subgroupFixedFieldCoefficients K C F H) 2
      (relativeFundamentalOrdinaryClass T S E C Fₕ) =
        groupCohomology.map H.subtype (𝟙 MH) 2
          (relativeFundamentalOrdinaryClass R S K C F) := by
  have hr := relativeFundamentalOrdinaryClass_restriction R T S K C E Fₕ p
  rw [← hr]
  change (groupCohomology.map (AlgEquiv.restrictScalarsHom K)
    (relativeRestrictionCoefficients K C E Fₕ) 2 ≫
      groupCohomology.map (e).toMonoidHom (subgroupFixedFieldCoefficients K C F H) 2) _ = _
  rw [← groupCohomology.map_comp]
  have he := groupCohomology.map_congr (A := M) (B := MH)
    (f := (AlgEquiv.restrictScalarsHom K).comp (e).toMonoidHom) (g := H.subtype)
    (φ := (Rep.resFunctor (e).toMonoidHom).map (relativeRestrictionCoefficients K C E Fₕ) ≫
      subgroupFixedFieldCoefficients K C F H) (ψ := 𝟙 MH)
    (subgroupFixedFieldEquiv_restrictScalars F H) rfl 2
  rw [he]
  rfl

/-- The degree-minus-two fundamental cups commute with the fixed-field identification. -/
theorem subgroupFixedField_cup (x : tateCohomology (Rep.trivial ℤ H ℤ) (-2)) :
    tateZeroGroupEquivalence MF MH e (subgroupFixedFieldCoefficients K C F H)
      (relativeFundamentalTateCupNegTwoEquiv T S E C Fₕ p
        (tateScalarMap (e).toMonoidHom x)) = relativeSubgroupCupEquiv R S K C F p H x := by
  change tateZeroGroupEquivalence MF MH e (subgroupFixedFieldCoefficients K C F H)
    (tateTwoClassMap MF (relativeFundamentalOrdinaryClass T S E C Fₕ) (-2)
      (tateScalarMap (e).toMonoidHom x)) =
    tateTwoClassMap MH _ (-2) x
  rw [tateTwoClassMap_groupEquivalence, subgroupFixedField_fundamentalClass R S K C F p H]

end LocalClassFieldTheory
