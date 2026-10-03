/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CoinducedInvariantSequence
public import FLT.LocalClassFieldTheory.OneCocycleInvariantSequence
public import FLT.LocalClassFieldTheory.RelativeSubgroupCupIso

/-!
# Quotient sequences for the local fundamental class

The actual local fundamental extension supplies the vanishing needed for
both invariant short exact sequences. The second sequence uses the divided
integer projection. No exactness or isomorphism is supplied by the caller.
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
local notation "Q" => shiftedCoefficients M
local notation "b" => shiftedTwoCocycle M c

variable (N : Subgroup Gal(F/K)) [N.Normal] [Fintype N]

include R S p in
omit [N.Normal] in
/-- The shifted coefficients have vanishing subgroup Tate H⁰. -/
theorem relativeFundamentalShifted_subgroup_zero :
    Limits.IsZero (tateCohomology (Rep.res N.subtype Q) 0) := by
  have hi := relativeSubgroupCup_isIso R S K C F p N (-1)
  have hz : Limits.IsZero (tateCohomology (Rep.res N.subtype M) 1) :=
    (tateScalar_neg_one_isZero N).of_iso
      (asIso (relativeSubgroupCup R S K C F N (-1))).symm
  exact hz.of_iso (coinducedSubgroupShift M N 0)

include R S p in
omit [Fintype N] in
/-- The first quotient coefficient sequence is short exact by the proved subgroup vanishing. -/
theorem relativeFundamentalInvariantCoefficients_shortExact :
    (coinducedInvariantSequence M N).ShortExact := by
  classical
  let : Fintype N := Fintype.ofFinite N
  exact coinducedInvariantSequence_shortExact M N
    (relativeFundamentalShifted_subgroup_zero R S K C F p N)

/-- The actual second quotient sequence has its scalar projection divided in ℤ. -/
def relativeFundamentalInvariantSequence : ShortComplex (Rep ℤ (Gal(F/K) ⧸ N)) :=
  oneCocycleInvariantSequence Q b N
    (relativeFundamentalExtension_allSubgroup_isZero R S K C F p N 0)

/-- The local arithmetic hypotheses prove short exactness of the divided quotient extension. -/
theorem relativeFundamentalInvariantSequence_shortExact :
    (relativeFundamentalInvariantSequence R S K C F p N).ShortExact :=
  oneCocycleInvariantSequence_shortExact Q b N
    (relativeFundamentalExtension_allSubgroup_isZero R S K C F p N 0)

/-- The two-class constructed by the two invariant exact sequences and the scalar unit. -/
def relativeFundamentalInvariantTwoClass :
    groupCohomology (Rep.quotientToInvariants M N) 2 :=
  groupCohomology.δ (relativeFundamentalInvariantCoefficients_shortExact R S K C F p N)
    1 2 rfl
    (groupCohomology.δ (relativeFundamentalInvariantSequence_shortExact R S K C F p N)
      0 1 rfl
      ((groupCohomology.H0Iso (Rep.trivial ℤ (Gal(F/K) ⧸ N) ℤ)).inv
        ⟨(1 : ℤ), fun _ => rfl⟩))

end LocalClassFieldTheory
