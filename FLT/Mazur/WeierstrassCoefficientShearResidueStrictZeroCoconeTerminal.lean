/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCoconeLines
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictConicDetection
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictTerminalDetection
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictConicDetection
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictTerminalDetection
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroAtlasCompatibility
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroAtlasMaps

import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCoconeGluing

import all FLT.Mazur.WeierstrassCoefficientShearResidueTerminal
import all FLT.Mazur.WeierstrassCoefficientShearRootTerminalComponents
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroRetainedDescent

import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCoconeLines
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroFirstCoconeDescent

/-!
# Full projective restrictions on the independent strict terminal pair

Both terminal components retain their full affine charts and distinct cyclic positions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (0 + (s + 1)) < depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth)
  (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDilatation
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 3) (by omega))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 3)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 3) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 3) (by omega) C.inl C.inr C.condition i

local notation "A" => coefficientShearAtlasMap hπ data Q r (s + 1) hs
local notation "D" => coefficientShearResidueStrictZeroAtlasCoconeMap
  hπ hm data s hs hk h3 h4 h6 hc C
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)

local notation "cover" => coefficientShearGluingCover hπ data Q r (s + 1) hs
local notation "G" => coefficientShearGluedIso hπ data Q r (s + 1) hs

local notation "M" => coefficientShearResidueStrictZeroGluedCoconeDesc
  hπ hm data s hs hk h3 h4 h6 hc C
local notation "T" => coefficientShearResidueTerminalComponent
  hπ hm data s hs hk h3 h4 h6 hc
local notation "ρ" => ProjectiveLine.endpointReversal Q

/-- The entire first terminal component recovers the reversed first middle cyclic input. -/
theorem coefficientShearResidueStrictZeroGluedCoconeDesc_terminal_first :
    T 0 ≫ M = ρ ≫ F ⟨s + 1, by omega⟩ := by
  apply pushout.hom_ext
  · change ProjectiveLine.left Q ≫ T 0 ≫ M =
      ProjectiveLine.left Q ≫ ρ ≫ F ⟨s + 1, by omega⟩
    rw [ProjectiveLine.left_endpointReversal_assoc]
    by_cases hs0 : s = 0
    · subst s
      rw [coefficientShearResidueTerminalComponent_zero_first_left_assoc
        hπ hm data 0 hs hk h3 h4 h6 hc (by omega)]
      simp only [coefficientConicFirstParameter,
        coefficientShearRetainedScaleOneConic, coefficientShearRetainedTensorChart,
        Category.assoc]
      rw [coefficientShearResidueStrictZeroGluedCoconeDesc_chart,
        coefficientShearResidueStrictZeroAtlasCoconeMap]
      change _ ≫ _ ≫ _ ≫ _ ≫ _ ≫ coefficientShearResidueStrictZeroFirstCoconeDesc
        hπ hm data 0 hs hk h3 h4 h6 hc C = _
      simpa only [coefficientShearRetainedScaleOneTensorIso, Category.assoc] using
        coefficientShearResidueStrictZeroFirstCoconeDesc_first
          hπ hm data 0 hs hk h3 h4 h6 hc C
    · rw [coefficientShearResidueTerminalComponent_first_left_assoc
        hπ hm data s hs hk h3 h4 h6 hc (by omega)]
      simp only [coefficientConicFirstParameter, coefficientShearRetainedConic,
        coefficientShearRetainedFiber, Category.assoc]
      rw [coefficientShearResidueStrictZeroGluedCoconeDesc_chart,
        coefficientShearResidueStrictZeroAtlasCoconeMap_positive_index
          hπ hm data s hs hk h3 h4 h6 hc C ⟨s, Nat.lt_succ_self s⟩ (by dsimp; omega)]
      simpa only [coefficientShearRetainedEquationIso, Category.assoc] using
        coefficientShearResidueStrictZeroRetainedDesc_first_conic
          hπ hm data s hs hk h3 h4 h6 hc ⟨s, Nat.lt_succ_self s⟩ (by dsimp; omega) F w
  · change ProjectiveLine.right Q ≫ T 0 ≫ M =
      ProjectiveLine.right Q ≫ ρ ≫ F ⟨s + 1, by omega⟩
    rw [ProjectiveLine.right_endpointReversal_assoc,
      coefficientShearResidueTerminalComponent_first_right_assoc,
      ← coefficientShearTerminalEquationSecond_chart_assoc,
      coefficientShearResidueStrictZeroGluedCoconeDesc_chart,
      coefficientShearResidueStrictZeroAtlasCoconeMap_divided]
    exact coefficientShearResidueStrictDividedDesc_second
      hπ hm data s hs hk h3 h4 h6 hc s (2 * s + 3) (by omega) F w

/-- The entire opposite terminal component recovers the independent second middle input. -/
theorem coefficientShearResidueStrictZeroGluedCoconeDesc_terminal_second :
    T 1 ≫ M = F ⟨s + 2, by omega⟩ := by
  apply pushout.hom_ext
  · change ProjectiveLine.left Q ≫ T 1 ≫ M =
      ProjectiveLine.left Q ≫ F ⟨s + 2, by omega⟩
    by_cases hs0 : s = 0
    · subst s
      rw [coefficientShearResidueTerminalComponent_zero_second_left_assoc
        hπ hm data 0 hs hk h3 h4 h6 hc (by omega)]
      simp only [coefficientConicSecondParameter,
        coefficientShearRetainedScaleOneConic, coefficientShearRetainedTensorChart,
        Category.assoc]
      rw [coefficientShearResidueStrictZeroGluedCoconeDesc_chart,
        coefficientShearResidueStrictZeroAtlasCoconeMap]
      change _ ≫ _ ≫ _ ≫ _ ≫ _ ≫ coefficientShearResidueStrictZeroFirstCoconeDesc
        hπ hm data 0 hs hk h3 h4 h6 hc C = _
      simpa only [coefficientShearRetainedScaleOneTensorIso, Category.assoc] using
        coefficientShearResidueStrictZeroFirstCoconeDesc_second
          hπ hm data 0 hs hk h3 h4 h6 hc C
    · rw [coefficientShearResidueTerminalComponent_second_left_assoc
        hπ hm data s hs hk h3 h4 h6 hc (by omega)]
      simp only [coefficientConicSecondParameter, coefficientShearRetainedConic,
        coefficientShearRetainedFiber, Category.assoc]
      rw [coefficientShearResidueStrictZeroGluedCoconeDesc_chart,
        coefficientShearResidueStrictZeroAtlasCoconeMap_positive_index
          hπ hm data s hs hk h3 h4 h6 hc C ⟨s, Nat.lt_succ_self s⟩ (by dsimp; omega)]
      simpa only [coefficientShearRetainedEquationIso, Category.assoc,
        show 2 * s + 2 - s = s + 2 from by omega] using
        coefficientShearResidueStrictZeroRetainedDesc_second_conic
          hπ hm data s hs hk h3 h4 h6 hc ⟨s, Nat.lt_succ_self s⟩ (by dsimp; omega) F w
  · change ProjectiveLine.right Q ≫ T 1 ≫ M =
      ProjectiveLine.right Q ≫ F ⟨s + 2, by omega⟩
    rw [coefficientShearResidueTerminalComponent_second_right_assoc,
      ← coefficientShearTerminalEquationFirst_chart_assoc,
      coefficientShearResidueStrictZeroGluedCoconeDesc_chart,
      coefficientShearResidueStrictZeroAtlasCoconeMap_divided]
    exact coefficientShearResidueStrictDividedDesc_first
      hπ hm data s hs hk h3 h4 h6 hc s (2 * s + 3) (by omega) F w

end FLT.Mazur.WeierstrassDividedDepth
