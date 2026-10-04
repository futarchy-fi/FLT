/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedCarryFundamentalClass
public import FLT.LocalClassFieldTheory.PositiveFiniteArtin
public import FLT.LocalClassFieldTheory.TateScalarGeneratorComparison

/-!
# Finite reciprocity at arithmetic Frobenius

The original inverse-cup map sends a uniformizer to negative Frobenius.
The explicitly negated normalization sends it to positive Frobenius.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory groupCohomology

variable (R S K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]
  {π : R} (hπ : Irreducible π) (n : UnramifiedIndex)

local notation "U" => maximalUnramified R K C
local notation "E" => unramifiedStage R K C n.degree
local notation "F" => unramifiedFiniteStage R K C n

attribute [local instance] relativeBaseTower
  unramifiedOriginalCarryFinite unramifiedOriginalCarryGalois
  unramifiedOriginalCarryTopology unramifiedOriginalCarryDiscrete
  unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete
  trivialCoefficientAction trivialCoefficientIntComm trivialCoefficientContinuous

local notation "M" => Rep.ofAlgebraAutOnUnits K E
local notation "e" => unramifiedOriginalCarryCoordinate R K C n
local notation "x" => finiteUnitInvariantInclusion K E (Additive.ofMul (fractionUniformizer R K hπ))

/-- Arithmetic Frobenius transported along the canonical presentation of the finite stage. -/
def unramifiedOriginalFrobenius : Gal(E/K) :=
  (AlgEquiv.autCongr (unramifiedCarryFieldEquiv R K C n)).symm
    (unramifiedStageFrobenius R K C n)

/-- This arithmetic Frobenius has positive cyclic coordinate one. -/
theorem unramifiedOriginalFrobenius_coordinate :
    e (unramifiedOriginalFrobenius R K C n) = Multiplicative.ofAdd 1 := by
  change (unramifiedStageCyclicEquiv R K C n).symm
    ((AlgEquiv.autCongr (unramifiedCarryFieldEquiv R K C n))
      ((AlgEquiv.autCongr (unramifiedCarryFieldEquiv R K C n)).symm _)) = _
  rw [MulEquiv.apply_symm_apply, unramifiedStageCyclicEquiv_frobenius]

variable [Algebra S (unramifiedStage R K C n.degree)]
  [IsFractionRing S (unramifiedStage R K C n.degree)] [Algebra S C]
  [IsScalarTower S (unramifiedStage R K C n.degree) C]
  [IsScalarTower R S (unramifiedStage R K C n.degree)] [IsScalarTower R S C]
  [Finite (ResidueField S)] [IsAdicComplete (maximalIdeal S) S]
  [CharZero C] (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]

local notation "Fr" => unramifiedOriginalFrobenius R K C n

include p in
/-- The actual relative fundamental cup has the negative Tate sign at arithmetic Frobenius. -/
theorem unramifiedFundamentalCup_frobenius (hn : 1 < n.degree) :
    relativeFundamentalTateCup R S K C E (-2)
      (tateScalarGenerator ℤ Gal(E/K) Fr) = -tateInvariantClass M x := by
  rw [unramifiedCarry_relativeFundamentalTateCup R S K C hπ n p]
  exact invariantCoefficientCarry_positive_generator M n.degree e hn x Fr
    (unramifiedOriginalFrobenius_coordinate R K C n)

variable [CharP (ResidueField S) p]

/-- Evaluation of the existing Artin map exposes its inverse-Frobenius convention. -/
theorem finiteArtin_unramified_uniformizer (hn : 1 < n.degree) :
    finiteArtin R S K C E p (Additive.ofMul (fractionUniformizer R K hπ)) =
      -Additive.ofMul (Abelianization.of Fr) := by
  have hc : (relativeFundamentalTateCupNegTwoEquiv R S K C E p).symm
      (tateInvariantClass M x) = -tateScalarGenerator ℤ Gal(E/K) Fr := by
    apply (relativeFundamentalTateCupNegTwoEquiv R S K C E p).injective
    rw [LinearEquiv.apply_symm_apply, map_neg,
      relativeFundamentalTateCupNegTwoEquiv_apply,
      unramifiedFundamentalCup_frobenius R S K C hπ n p hn, neg_neg]
  change tateScalarAbelianizationEquiv Gal(E/K)
    ((relativeFundamentalTateCupNegTwoEquiv R S K C E p).symm (tateInvariantClass M x)) = _
  rw [hc, map_neg, tateScalarAbelianizationEquiv_generator]

/-- Positive finite reciprocity sends the base uniformizer to arithmetic Frobenius. -/
theorem positiveFiniteArtin_unramified_uniformizer (hn : 1 < n.degree) :
    positiveFiniteArtin R S K C E p (Additive.ofMul (fractionUniformizer R K hπ)) =
      Additive.ofMul (Abelianization.of Fr) := by
  rw [positiveFiniteArtin_apply, finiteArtin_unramified_uniformizer R S K C hπ n p hn,
    neg_neg]

/-- Positive Frobenius normalization also includes the trivial degree-one stage. -/
theorem positiveFiniteArtin_unramified_uniformizer_all_degrees :
    positiveFiniteArtin R S K C E p (Additive.ofMul (fractionUniformizer R K hπ)) =
      Additive.ofMul (Abelianization.of Fr) := by
  by_cases hn : 1 < n.degree
  · exact positiveFiniteArtin_unramified_uniformizer R S K C hπ n p hn
  have hd : (n.degree : ℕ) = 1 := by
    change ¬1 < (n.degree : ℕ) at hn
    have := n.degree.pos
    omega
  have hc : Nat.card Gal(E/K) = 1 := by
    rw [IsGalois.card_aut_eq_finrank, finrank_unramifiedStage, hd]
  let : Subsingleton Gal(E/K) := (Nat.card_eq_one_iff_unique.mp hc).1
  let : Subsingleton (Abelianization Gal(E/K)) :=
    Function.Surjective.subsingleton (QuotientGroup.mk'_surjective _)
  exact Subsingleton.elim _ _

end LocalClassFieldTheory
