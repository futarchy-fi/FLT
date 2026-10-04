/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.PositiveFiniteArtin
public import FLT.LocalClassFieldTheory.FiniteParameterCarry
public import FLT.LocalClassFieldTheory.NegativeCupArithmetic
public import FLT.LocalClassFieldTheory.TateScalarGeneratorComparison

/-!
# Cyclic character coordinates for positive finite reciprocity

Generation of relative H² and evaluation of the negative carry cup determine
reciprocity for every parameter of a cyclic extension.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory groupCohomology

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

variable {n : ℕ} [NeZero n] (χ : Gal(F/K) →* Multiplicative (ZMod n))
  (hχ : Function.Bijective χ) (u : Additive Kˣ)

local notation "x" => finiteUnitInvariantInclusion K F u
local notation "c" => finiteParameterCarryClass χ (Additive Fˣ) x

omit [CharP (ResidueField R) p] in
include p in
/-- A carry is a natural multiple of the independently constructed fundamental class. -/
theorem finiteParameterCarry_fundamental_multiple :
    ∃ m : ℕ, m • relativeFundamentalClass R S K C F = c := by
  let : NeZero (Module.finrank K F) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨z, hz⟩ := (relativeFundamentalEquiv R S K C F p).surjective c
  refine ⟨z.val, ?_⟩
  rw [← hz]
  change z.val • relativeFundamentalEquiv R S K C F p 1 = _
  rw [← map_nsmul]
  congr 1
  simp

include hχ in
/-- The carry class and positive reciprocity have the same cyclic coordinate. -/
theorem cyclicCharacterArtin_coordinate (hn : 1 < n) :
    ∃ m : ℕ, m • relativeFundamentalClass R S K C F = c ∧
      finiteCharacterAbelianization χ (positiveFiniteArtin R S K C F p u) = (m : ZMod n) := by
  obtain ⟨m, hm⟩ := finiteParameterCarry_fundamental_multiple R S K C F p χ u
  obtain ⟨g, hg⟩ := hχ.surjective (Multiplicative.ofAdd 1)
  let e : Gal(F/K) ≃* Multiplicative (ZMod n) := MulEquiv.ofBijective χ hχ
  have ho : H2π M (finiteParameterCarry χ (Additive Fˣ) x) =
      m • relativeFundamentalOrdinaryClass R S K C F := by
    refine (finiteParameterCarryClass_ordinary χ (Additive Fˣ) x).symm.trans ?_
    rw [← hm, map_nsmul]
    rfl
  have hc : m • relativeFundamentalTateCup R S K C F (-2)
      (tateScalarGenerator ℤ Gal(F/K) g) = -tateInvariantClass M x := by
    change m • tateTwoClassMap M (relativeFundamentalOrdinaryClass R S K C F) (-2) _ = _
    rw [← tateTwoClassMap_negTwo_nsmul, ← ho, tateTwoClassMap_class]
    exact invariantCoefficientCarry_positive_generator M n e hn x g hg
  have hi : (relativeFundamentalTateCupNegTwoEquiv R S K C F p).symm
      (tateInvariantClass M x) = -(m • tateScalarGenerator ℤ Gal(F/K) g) := by
    apply (relativeFundamentalTateCupNegTwoEquiv R S K C F p).injective
    rw [LinearEquiv.apply_symm_apply, map_neg, map_nsmul,
      relativeFundamentalTateCupNegTwoEquiv_apply, hc, neg_neg]
  have ha : positiveFiniteArtin R S K C F p u =
      m • Additive.ofMul (Abelianization.of g) := by
    change -tateScalarAbelianizationEquiv Gal(F/K)
      ((relativeFundamentalTateCupNegTwoEquiv R S K C F p).symm
        (tateInvariantClass M x)) = _
    rw [hi, map_neg, map_nsmul, neg_neg, tateScalarAbelianizationEquiv_generator]
  refine ⟨m, hm, ?_⟩
  rw [ha, map_nsmul, finiteCharacterAbelianization_of, hg]
  simp

end LocalClassFieldTheory
