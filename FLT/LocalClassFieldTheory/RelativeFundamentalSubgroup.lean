/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteSubfieldDvr
public import FLT.LocalClassFieldTheory.RelativeFundamentalExtensionRestriction
public import FLT.LocalClassFieldTheory.SubgroupFixedFieldTower
public import FLT.LocalClassFieldTheory.TateGroupEquivalence

/-!
# Adjacent vanishing on every subgroup

For each subgroup, construct the fixed field and its complete integer DVR.
The field-wise theorem and the actual Galois identification then give vanishing
for the restriction of the original fundamental extension to that subgroup.
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

set_option maxHeartbeats 1600000 in
-- Comparing the two concrete restricted quotient actions expands their homology constructions.
include p in
/-- Every subgroup of the original Galois group has zero adjacent Tate groups. -/
theorem relativeFundamentalExtension_subgroup_isZero
    (n : ℤ) (hn : n = 0 ∨ n = 1) :
    Limits.IsZero (tateCohomology
      (Rep.res H.subtype (relativeFundamentalExtension R S K C F)) n) := by
  classical
  let : Algebra E F := inferInstanceAs (Algebra E Fₕ)
  let : IsScalarTower K E F := inferInstanceAs (IsScalarTower K E Fₕ)
  let : IsScalarTower E F C := inferInstanceAs (IsScalarTower E Fₕ C)
  let : FiniteDimensional K E := FiniteDimensional.of_injective
    (IntermediateField.inclusion (subgroupFixedField_le F H)).toLinearMap
    (IntermediateField.inclusion_injective (subgroupFixedField_le F H))
  let : IsScalarTower R E F := IsScalarTower.of_algebraMap_eq fun r => by
    apply (algebraMap F C).injective
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  let : IsGalois K Fₕ := inferInstanceAs (IsGalois K F)
  let : FiniteDimensional K Fₕ := inferInstanceAs (FiniteDimensional K F)
  let : FiniteDimensional E Fₕ := FiniteDimensional.right K E Fₕ
  let : Algebra S Fₕ := inferInstanceAs (Algebra S F)
  let : IsFractionRing S Fₕ := inferInstanceAs (IsFractionRing S F)
  let : IsScalarTower S Fₕ C := inferInstanceAs (IsScalarTower S F C)
  let : TopologicalSpace (Additive Fₕˣ) := inferInstanceAs (TopologicalSpace (Additive Fˣ))
  let : DiscreteTopology (Additive Fₕˣ) := inferInstanceAs (DiscreteTopology (Additive Fˣ))
  let : IsGalois E Fₕ := IsGalois.tower_top_of_isGalois K E Fₕ
  let : Algebra T S := finiteSubfieldDvrAlgebra R S E F
  let : IsScalarTower R T S := finiteSubfieldDvr_baseTower R S E F
  let : IsScalarTower T S F := finiteSubfieldDvr_fieldTower R S E F
  let : Module.Finite T S := finiteSubfieldDvr_topFinite R S E
  let : FaithfulSMul T S := finiteSubfieldDvr_faithful R S E F
  let : IsLocalRing T := finiteSubfieldDvr_local R S E
  let : IsDiscreteValuationRing T := finiteSubfieldDvr_discrete R K E
  let : Module.Finite R T := finiteSubfieldDvr_finite R K E
  let : IsFractionRing T E := finiteSubfieldDvr_fractionRing R K E
  let : FaithfulSMul R T := intermediateDvrBaseFaithful R K C E
  let : Finite (ResidueField T) := finiteSubfieldDvr_residueFinite R S E
  let : CharP (ResidueField T) p := finiteSubfieldDvr_residueChar R S E p
  let : IsAdicComplete (maximalIdeal T) T := finiteSubfieldDvr_complete R K E
  let : IsScalarTower T S C := IsScalarTower.of_algebraMap_eq fun t => by
    change (algebraMap F C) ((algebraMap T F) t) = _
    rw [IsScalarTower.algebraMap_apply T S F, ← IsScalarTower.algebraMap_apply S F C]
  let : IsGalois K ((Fₕ).restrictScalars K) := inferInstanceAs (IsGalois K F)
  let : FiniteDimensional K ((Fₕ).restrictScalars K) :=
    inferInstanceAs (FiniteDimensional K F)
  have hz := relativeFundamentalExtension_restriction_isZero R T S K C E Fₕ p n hn
  let M := relativeFundamentalExtension R S K C F
  let f : Gal(Fₕ/E) →* Gal(F/K) := AlgEquiv.restrictScalarsHom K
  let e := subgroupFixedFieldEquiv F H
  have ht := hz.of_iso (tateGroupEquivalenceIso (Rep.res f M) e n).symm
  have he : Rep.res e.toMonoidHom (Rep.res f M) = Rep.res H.subtype M := by
    change Rep.res (f.comp e.toMonoidHom) M = Rep.res H.subtype M
    rw [subgroupFixedFieldEquiv_restrictScalars]
  exact ht.of_iso ((tateCohomologyFunctor n).mapIso (eqToIso he)).symm

end LocalClassFieldTheory
