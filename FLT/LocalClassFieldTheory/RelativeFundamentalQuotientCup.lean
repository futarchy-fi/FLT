/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.NegativeCupQuotient
public import FLT.LocalClassFieldTheory.RelativeSubgroupCupIso

/-!
# The descended local fundamental cup is an isomorphism

Exactness of the scalar and norm quotient sequences, and the proved ambient
and subgroup cups, give a genuine quotient equivalence without a coprimality
assumption. It remains distinct from cup by a separately normalized quotient
fundamental class until their comparison is proved.
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

include p in
/-- The descended local fundamental cup is surjective for every normal subgroup. -/
theorem relativeFundamentalQuotientCup_surjective : Function.Surjective CQ := by
  intro y
  obtain ⟨z, rfl⟩ := tateZeroDeflation_surjective M N y
  obtain ⟨x, rfl⟩ := (relativeFundamentalTateCupNegTwoEquiv R S K C F p).surjective z
  exact ⟨tateScalarMap q x, negativeCupQuotient_scalarMap M N a x⟩

include p in
/-- Exactness and the subgroup cup prove injectivity without cancelling any degree. -/
theorem relativeFundamentalQuotientCup_injective : Function.Injective CQ := by
  classical
  let : Fintype N := Fintype.ofFinite N
  apply (injective_iff_map_eq_zero CQ).mpr
  intro x hx
  obtain ⟨y, rfl⟩ := tateScalarMap_quotient_surjective N x
  rw [negativeCupQuotient_scalarMap] at hx
  obtain ⟨z, hz⟩ := (tateZeroDeflation_eq_zero_iff M N _).mp hx
  obtain ⟨w, hw⟩ := (relativeSubgroupCupEquiv R S K C F p N).surjective z
  change tateTwoClassMap (Rep.res N.subtype M)
    (groupCohomology.map N.subtype (𝟙 (Rep.res N.subtype M)) 2 a) (-2) w = z at hw
  have he : tateScalarMap N.subtype w = y := by
    apply (relativeFundamentalTateCupNegTwoEquiv R S K C F p).injective
    change tateTwoClassMap M a (-2) (tateScalarMap N.subtype w) =
      tateTwoClassMap M a (-2) y
    rw [← tateTwoClassMap_corestriction M N a w, hw, hz]
  exact (tateScalarMap_quotient_eq_zero_iff N y).mpr ⟨w, he⟩

/-- The actual unscaled descended fundamental cup as an additive equivalence. -/
def relativeFundamentalQuotientCupEquiv :
    tateCohomology (Rep.trivial ℤ (Gal(F/K) ⧸ N) ℤ) (-2) ≃+
      tateCohomology ((M).quotientToInvariants N) 0 :=
  AddEquiv.ofBijective CQ
    ⟨relativeFundamentalQuotientCup_injective R S K C F p N,
      relativeFundamentalQuotientCup_surjective R S K C F p N⟩

/-- The quotient equivalence commutes with the ambient cup and actual deflation. -/
theorem relativeFundamentalQuotientCupEquiv_scalarMap
    (x : tateCohomology (Rep.trivial ℤ Gal(F/K) ℤ) (-2)) :
    relativeFundamentalQuotientCupEquiv R S K C F p N (tateScalarMap q x) =
      tateZeroDeflation M N (relativeFundamentalTateCup R S K C F (-2) x) :=
  negativeCupQuotient_scalarMap M N a x

/-- Inverting the proved quotient square introduces no subgroup-order factor. -/
theorem relativeFundamentalQuotientCupEquiv_symm_deflation
    (y : tateCohomology M 0) :
    (relativeFundamentalQuotientCupEquiv R S K C F p N).symm (tateZeroDeflation M N y) =
      tateScalarMap q ((relativeFundamentalTateCupNegTwoEquiv R S K C F p).symm y) := by
  apply (relativeFundamentalQuotientCupEquiv R S K C F p N).injective
  rw [AddEquiv.apply_symm_apply, relativeFundamentalQuotientCupEquiv_scalarMap]
  change tateZeroDeflation M N y = tateZeroDeflation M N
    (relativeFundamentalTateCupNegTwoEquiv R S K C F p
      ((relativeFundamentalTateCupNegTwoEquiv R S K C F p).symm y))
  rw [LinearEquiv.apply_symm_apply]

end LocalClassFieldTheory
