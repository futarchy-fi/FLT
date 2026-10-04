/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RelativeFundamentalCupIso
public import FLT.LocalClassFieldTheory.TwoExtensionCorestriction

/-!
# The restricted fundamental cup on subgroup Tate groups

Acyclicity of the original restricted extension and the proved coefficient
comparison make the actual restricted-class cup invertible.
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
local notation "c" => twoClassRepresentative M (relativeFundamentalOrdinaryClass R S K C F)

variable (H : Subgroup Gal(F/K)) [Fintype H]

local notation "MH" => Rep.res H.subtype M
local notation "cr" => groupCohomology.mapCocycles₂ H.subtype (𝟙 MH) c

/-- Cup with the restriction of the actual ordinary local fundamental class. -/
def relativeSubgroupCup (n : ℤ) :
    tateCohomology (Rep.trivial ℤ H ℤ) n ⟶ tateCohomology MH (n + 2) :=
  tateTwoClassMap MH (groupCohomology.map H.subtype (𝟙 MH) 2
    (relativeFundamentalOrdinaryClass R S K C F)) n

omit [CharZero C] in
/-- The restricted chosen representative computes the subgroup cup. -/
theorem relativeSubgroupCup_representative (n : ℤ) :
    relativeSubgroupCup R S K C F H n = tateTwoExtensionMap MH cr n := by
  have hc := twoClassRepresentative_spec M (relativeFundamentalOrdinaryClass R S K C F)
  have hr := congrArg (fun f => f.hom c) (groupCohomology.H2π_comp_map H.subtype (𝟙 MH))
  change groupCohomology.map H.subtype (𝟙 MH) 2 (groupCohomology.H2π M c) =
    groupCohomology.H2π MH cr at hr
  rw [hc] at hr
  change tateTwoClassMap MH _ n = _
  rw [hr, tateTwoClassMap_class]

include p in
/-- The subgroup cup is invertible, using the original extension's proved acyclicity. -/
theorem relativeSubgroupCup_isIso (n : ℤ) :
    IsIso (relativeSubgroupCup R S K C F H n) := by
  rw [relativeSubgroupCup_representative, tateTwoExtensionMap_eq_shift]
  have hδ : IsIso (TateCohomology.δ
      (twoExtensionRestriction_shortExact M H.subtype c) n) :=
    ShortComplex.SnakeInput.isIso_δ _
      (relativeFundamentalExtension_allSubgroup_isZero R S K C F p H n)
      (relativeFundamentalExtension_allSubgroup_isZero R S K C F p H (n + 1))
  have := shiftedRestriction_isIso M H.subtype Subtype.val_injective (n + 1)
  have : IsIso (TateCohomology.δ
      (oneCocycleSequence_shortExact (shiftedCoefficients MH) (shiftedTwoCocycle MH cr)) n) := by
    rw [← twoExtensionRestriction_boundary M H.subtype c n]
    infer_instance
  infer_instance

/-- The proved degree-minus-two subgroup cup equivalence. -/
def relativeSubgroupCupEquiv :
    tateCohomology (Rep.trivial ℤ H ℤ) (-2) ≃ₗ[ℤ] tateCohomology MH 0 := by
  have := relativeSubgroupCup_isIso R S K C F p H (-2)
  exact (asIso (relativeSubgroupCup R S K C F H (-2))).toLinearEquiv

end LocalClassFieldTheory
