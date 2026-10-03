/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RelativeFundamentalOrdinaryRestriction
public import FLT.LocalClassFieldTheory.RelativeFundamentalExtension
public import FLT.LocalClassFieldTheory.TwoExtensionSubgroupVanishing
public import FLT.LocalClassFieldTheory.TwoExtensionRepresentativeIso

/-!
# Adjacent vanishing for the restricted local fundamental extension

Restriction carries the ordinary fundamental class to the one over the
intermediate field. The concrete extension comparison and representative
translation therefore transport the proved degree-zero and degree-one vanishing.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory groupCohomology

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

attribute [local instance] relativeFundamentalRestrictionFinite
  relativeFundamentalRestrictionFiniteOverBase relativeFundamentalRestrictionTopAlgebra
  relativeFundamentalRestrictionTopFractionRing relativeFundamentalRestrictionTopTower
  relativeFundamentalRestrictionBaseTower relativeFundamentalRestrictionMiddleTower
  relativeRestrictionGalois

variable [TopologicalSpace (Additive Fˣ)] [DiscreteTopology (Additive Fˣ)]

attribute [local instance] relativeFundamentalRestrictionUnitTopology
  relativeFundamentalRestrictionUnitDiscrete

variable [CharZero C] (p : ℕ) [Fact p.Prime]
  [CharP (ResidueField R) p] [CharP (ResidueField S) p] [CharP (ResidueField T) p]

local notation "M" => Rep.ofAlgebraAutOnUnits K (F.restrictScalars K)
local notation "f" => (AlgEquiv.restrictScalarsHom K : Gal(F/E) →* Gal(F/K))
local notation "Mr" => Rep.res f M
local notation "c" => twoClassRepresentative M
  (relativeFundamentalOrdinaryClass R T K C (F.restrictScalars K))
local notation "cr" => mapCocycles₂ f (𝟙 Mr) c
local notation "cE" => twoClassRepresentative (Rep.ofAlgebraAutOnUnits E F)
  (relativeFundamentalOrdinaryClass S T E C F)

set_option maxHeartbeats 800000 in
-- The two presentations of the coefficient representation require a large homology comparison.
include p in
omit [CharP (ResidueField T) p] in
/-- The restricted chosen cocycle and the new base's chosen cocycle have the same two-class. -/
theorem relativeFundamentalRepresentative_restriction : H2π Mr cr = H2π Mr cE := by
  have h := congrArg (fun u => u.hom c) (H2π_comp_map f (𝟙 Mr))
  change groupCohomology.map f (𝟙 Mr) 2 (H2π M c) = H2π Mr cr at h
  have hs := congrArg (groupCohomology.map f (𝟙 Mr) 2)
    (twoClassRepresentative_spec M
      (relativeFundamentalOrdinaryClass R T K C (F.restrictScalars K)))
  have hr := relativeFundamentalOrdinaryClass_restriction R S T K C E F p
  have ht := twoClassRepresentative_spec (Rep.ofAlgebraAutOnUnits E F)
    (relativeFundamentalOrdinaryClass S T E C F)
  have result := h.symm.trans (hs.trans (hr.trans ht.symm))
  exact result

set_option maxHeartbeats 1600000 in
-- The concrete restricted quotient actions occur in both the class and extension comparisons.
include S p in
/-- Both adjacent Tate groups of the actual restricted fundamental extension vanish. -/
theorem relativeFundamentalExtension_restriction_isZero (n : ℤ) (hn : n = 0 ∨ n = 1) :
    Limits.IsZero (tateCohomology
      (Rep.res f (relativeFundamentalExtension R T K C (F.restrictScalars K))) n) := by
  have hc := relativeFundamentalRepresentative_restriction R S T K C E F p
  have he : oneCocycleExtension (shiftedCoefficients Mr) (shiftedTwoCocycle Mr cE) =
      relativeFundamentalExtension S T E C F := by
    have h : (⟨Mr, cE⟩ : Σ N : Rep.{0} ℤ Gal(F/E), cocycles₂ N) =
        ⟨Rep.ofAlgebraAutOnUnits E F, cE⟩ :=
      Sigma.ext (show Mr = Rep.ofAlgebraAutOnUnits E F from rfl) (HEq.rfl)
    let ψ : (Σ N : Rep.{0} ℤ Gal(F/E), cocycles₂ N) → Rep.{0} ℤ Gal(F/E) := fun x =>
      oneCocycleExtension (shiftedCoefficients x.1) (shiftedTwoCocycle x.1 x.2)
    have he' := congrArg ψ h
    exact he'
  have hz : Limits.IsZero (tateCohomology (relativeFundamentalExtension S T E C F) n) := by
    rcases hn with rfl | rfl
    · exact relativeFundamentalExtension_tate_zero_isZero S T E C F p
    · exact relativeFundamentalExtension_tate_one_isZero S T E C F p
  have hz' := hz.of_iso ((tateCohomologyFunctor n).mapIso (eqToIso he))
  have hr := (twoExtensionRepresentative_isZero_iff Mr cr cE hc n).mpr hz'
  have result := twoExtensionSubgroup_isZero M f (AlgEquiv.restrictScalars_injective K) c n hr
  have hs : (oneCocycleSequence (shiftedCoefficients M) (shiftedTwoCocycle M c)).X₂ =
      relativeFundamentalExtension R T K C (F.restrictScalars K) := rfl
  let es := (Rep.resFunctor f).mapIso (eqToIso hs)
  exact result.of_iso ((tateCohomologyFunctor n).mapIso es).symm

end LocalClassFieldTheory
