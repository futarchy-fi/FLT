/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.InvariantTwoClassNegativeCup
public import FLT.LocalClassFieldTheory.RelativeFundamentalQuotientCup
public import FLT.LocalClassFieldTheory.RelativeFundamentalQuotientSequences
public import FLT.LocalClassFieldTheory.TwoExtensionDeflation

/-!
# The quotient fundamental class and its negative cup

The ordinary class of the actual invariant sequences realizes the unscaled
quotient cup. The local class formation proves its bijectivity.
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


variable [Fintype (Gal(F/K) ⧸ N)]

/-- The constructed quotient fundamental two-class realizes the descended negative cup. -/
theorem relativeFundamentalInvariantTwoClass_negativeCup
    (x : tateCohomology (Rep.trivial ℤ (Gal(F/K) ⧸ N) ℤ) (-2)) :
    tateTwoClassMap (Rep.quotientToInvariants M N)
      (relativeFundamentalInvariantTwoClass R S K C F p N) (-2) x =
    negativeCupQuotient M N (relativeFundamentalOrdinaryClass R S K C F) x := by
  have h := invariantTwoClassCup_eq_negativeCupQuotient M c N
    (relativeFundamentalShifted_subgroup_zero R S K C F p N)
    (relativeFundamentalExtension_allSubgroup_isZero R S K C F p N 0) x
  rw [twoClassRepresentative_spec] at h
  exact h

/-- The negative cup of the actual quotient two-class is bijective. -/
theorem relativeFundamentalInvariantTwoClass_negativeCup_bijective :
    Function.Bijective (tateTwoClassMap (Rep.quotientToInvariants M N)
      (relativeFundamentalInvariantTwoClass R S K C F p N) (-2)) := by
  have he : (tateTwoClassMap (Rep.quotientToInvariants M N)
      (relativeFundamentalInvariantTwoClass R S K C F p N) (-2) : _ → _) =
      negativeCupQuotient M N (relativeFundamentalOrdinaryClass R S K C F) :=
    funext (relativeFundamentalInvariantTwoClass_negativeCup R S K C F p N)
  rw [he]
  exact (relativeFundamentalQuotientCupEquiv R S K C F p N).bijective

/-- Its negative cup commutes with the ambient fundamental cup without a degree factor. -/
theorem relativeFundamentalInvariantTwoClass_negativeCup_deflation
    (x : tateCohomology (Rep.trivial ℤ Gal(F/K) ℤ) (-2)) :
    tateTwoClassMap (Rep.quotientToInvariants M N)
      (relativeFundamentalInvariantTwoClass R S K C F p N) (-2)
      (tateScalarMap (QuotientGroup.mk' N) x) =
    tateZeroDeflation M N (relativeFundamentalTateCup R S K C F (-2) x) := by
  rw [relativeFundamentalInvariantTwoClass_negativeCup, negativeCupQuotient_scalarMap]
  rfl

end LocalClassFieldTheory
