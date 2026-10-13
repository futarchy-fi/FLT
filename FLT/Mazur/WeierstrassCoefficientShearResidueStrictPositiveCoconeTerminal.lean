/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveCoconeLines
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictConicDetection
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictTerminalDetection
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictConicDetection
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictTerminalDetection
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveAtlasCompatibility
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveAtlasMaps

import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveCoconeGluing

import all FLT.Mazur.WeierstrassCoefficientShearResidueTerminal
import all FLT.Mazur.WeierstrassCoefficientShearRootTerminalComponents
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveRetainedDescent

import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveCoconeLines

/-!
# Full projective restrictions on every original adjacent component pair

Every original adjacent pair retains both full affine charts and its cyclic orientation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + (s + 1)) < depth)
  (hstart : 0 < start)
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
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 5) (by omega))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 5)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 5) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 5) (by omega) C.inl C.inr C.condition i

local notation "A" => coefficientShearAtlasMap hπ data Q r (s + 1) hs
local notation "D" => coefficientShearResidueStrictPositiveAtlasCoconeMap
  hπ hm data s hs hk hstart h3 h4 h6 hc C
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)

local notation "cover" => coefficientShearGluingCover hπ data Q r (s + 1) hs
local notation "G" => coefficientShearGluedIso hπ data Q r (s + 1) hs

local notation "M" => coefficientShearResidueStrictPositiveGluedCoconeDesc
  hπ hm data s hs hk hstart h3 h4 h6 hc C
local notation "T" => coefficientShearResidueTerminalComponent
  hπ hm data s hs hk h3 h4 h6 hc
local notation "ρ" => ProjectiveLine.endpointReversal Q

/-- The entire first terminal component recovers the reversed first middle cyclic input. -/
theorem coefficientShearResidueStrictPositiveGluedCoconeDesc_terminal_first :
    T 0 ≫ M = ρ ≫ F ⟨s + 2, by omega⟩ := by
  apply pushout.hom_ext
  · change ProjectiveLine.left Q ≫ T 0 ≫ M =
      ProjectiveLine.left Q ≫ ρ ≫ F ⟨s + 2, by omega⟩
    rw [ProjectiveLine.left_endpointReversal_assoc,
      coefficientShearResidueTerminalComponent_first_left_assoc
        hπ hm data s hs hk h3 h4 h6 hc (by omega)]
    simp only [coefficientConicFirstParameter, coefficientShearRetainedConic,
      coefficientShearRetainedFiber, Category.assoc]
    rw [coefficientShearResidueStrictPositiveGluedCoconeDesc_chart,
      coefficientShearResidueStrictPositiveAtlasCoconeMap_retained]
    simpa only [coefficientShearRetainedEquationIso, Category.assoc] using
      coefficientShearResidueStrictPositiveRetainedDesc_first_conic
        hπ hm data s hs hk h3 h4 h6 hc ⟨s, Nat.lt_succ_self s⟩ hstart F w
  · change ProjectiveLine.right Q ≫ T 0 ≫ M =
      ProjectiveLine.right Q ≫ ρ ≫ F ⟨s + 2, by omega⟩
    rw [ProjectiveLine.right_endpointReversal_assoc,
      coefficientShearResidueTerminalComponent_first_right_assoc,
      ← coefficientShearTerminalEquationSecond_chart_assoc,
      coefficientShearResidueStrictPositiveGluedCoconeDesc_chart,
      coefficientShearResidueStrictPositiveAtlasCoconeMap_divided]
    exact coefficientShearResidueStrictDividedDesc_second
      hπ hm data s hs hk h3 h4 h6 hc (s + 1) (2 * s + 5) (by omega) F w

/-- The entire opposite terminal component recovers the independent second middle input. -/
theorem coefficientShearResidueStrictPositiveGluedCoconeDesc_terminal_second :
    T 1 ≫ M = F ⟨s + 3, by omega⟩ := by
  apply pushout.hom_ext
  · change ProjectiveLine.left Q ≫ T 1 ≫ M =
      ProjectiveLine.left Q ≫ F ⟨s + 3, by omega⟩
    rw [coefficientShearResidueTerminalComponent_second_left_assoc
        hπ hm data s hs hk h3 h4 h6 hc (by omega)]
    simp only [coefficientConicSecondParameter, coefficientShearRetainedConic,
      coefficientShearRetainedFiber, Category.assoc]
    rw [coefficientShearResidueStrictPositiveGluedCoconeDesc_chart,
      coefficientShearResidueStrictPositiveAtlasCoconeMap_retained]
    simpa only [coefficientShearRetainedEquationIso, Category.assoc,
      show 2 * s + 3 - s = s + 3 from by omega] using
      coefficientShearResidueStrictPositiveRetainedDesc_second_conic
        hπ hm data s hs hk h3 h4 h6 hc ⟨s, Nat.lt_succ_self s⟩ hstart F w
  · change ProjectiveLine.right Q ≫ T 1 ≫ M =
      ProjectiveLine.right Q ≫ F ⟨s + 3, by omega⟩
    rw [coefficientShearResidueTerminalComponent_second_right_assoc,
      ← coefficientShearTerminalEquationFirst_chart_assoc,
      coefficientShearResidueStrictPositiveGluedCoconeDesc_chart,
      coefficientShearResidueStrictPositiveAtlasCoconeMap_divided]
    exact coefficientShearResidueStrictDividedDesc_first
      hπ hm data s hs hk h3 h4 h6 hc (s + 1) (2 * s + 5) (by omega) F w

end FLT.Mazur.WeierstrassDividedDepth
