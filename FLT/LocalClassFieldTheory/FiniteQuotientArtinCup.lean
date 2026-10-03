/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteQuotientArtin
public import FLT.LocalClassFieldTheory.RelativeFundamentalQuotientCup

/-!
# Quotient Artin and the descended fundamental cup

The existing projected Artin map is computed by the inverse of the proved
unscaled quotient cup on the actual norm quotient. This does not identify it
with the Artin map independently constructed over the fixed field.
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
local notation "a" => relativeFundamentalOrdinaryClass R S K C F

variable (N : Subgroup Gal(F/K)) [N.Normal] [Fintype (Gal(F/K) ⧸ N)]

local notation "q" => QuotientGroup.mk' N
local notation "CQ" => negativeCupQuotient M N a

/-- The existing quotient Artin map is the inverse descended cup on invariant units. -/
theorem finiteQuotientArtin_descendedCup (u : Additive Kˣ) :
    finiteQuotientArtin R S K C F p N u =
      tateScalarAbelianizationEquiv (Gal(F/K) ⧸ N)
        ((relativeFundamentalQuotientCupEquiv R S K C F p N).symm
          (tateInvariantClass ((M).quotientToInvariants N)
            (quotientInvariantEquiv M N (finiteUnitInvariantInclusion K F u)))) := by
  rw [← tateZeroDeflation_class, relativeFundamentalQuotientCupEquiv_symm_deflation]
  change _ = tateScalarAbelianizationEquiv (Gal(F/K) ⧸ N)
    ((tateScalarAbelianizationEquiv (Gal(F/K) ⧸ N)).symm _)
  rw [AddEquiv.apply_symm_apply]
  rfl

end LocalClassFieldTheory
