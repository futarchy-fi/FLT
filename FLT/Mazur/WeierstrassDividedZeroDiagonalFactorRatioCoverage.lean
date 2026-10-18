/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalFactorRatioInfinity
public import FLT.Mazur.WeierstrassDividedRevisedNodeCoverage

/-!
# The full actual source chart maps cover the independent diagonal polygon

Coverage uses the original infinity open, both original initial opens, both
retained nodes and the common terminal. This is a covering family; agreement
on source intersections remains a separate gluing obligation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "p" => arithmeticZeroDiagonalPolygonParameter hπ data H hj u hu m
local notation "A" => arithmeticZeroFiniteAtlasObject hπ data H m m hj u hu
local notation "Y" => arithmeticZeroDiagonalPolygon hπ data H m hj u hu
local notation "c" => arithmeticZeroDiagonalPolygonChart hπ data H m hj u hu
local notation "I" => arithmeticZeroDiagonalPolygonInitialChart hπ data H m hj u hu
local notation "L" => arithmeticZeroDiagonalPolygonRetainedChart hπ data H m hj u hu
local notation "T" => arithmeticZeroDiagonalPolygonTerminalChart hπ data H m hj u hu
local notation "C" => arithmeticZeroDiagonalPolygonInitialMap hπ data H m hj u hu
local notation "G" => arithmeticZeroDiagonalPolygonRetainedMap hπ data H m hj u hu

/-- Each named initial target node has the complete image of its raw cyclic label. -/
theorem arithmeticZeroDiagonalPolygonInitialChart_range (b : Bool) :
    Set.range (I b) = Set.range (c (initialPolygonIndex 1 b)) :=
  revisedPolygon_chartWithParameter_range 5 p (by omega) _ _ _

/-- Each named retained target node has the complete image of its raw cyclic label. -/
theorem arithmeticZeroDiagonalPolygonRetainedChart_range (b : Bool) :
    Set.range (L b) = Set.range (c (retainedPolygonIndex 1 0 b)) :=
  revisedPolygon_chartWithParameter_range 5 p (by omega) _ _ _

/-- The full common terminal has exactly the label-zero image. -/
theorem arithmeticZeroDiagonalPolygonTerminalChart_range : Set.range T = Set.range (c 0) :=
  revisedPolygon_chartWithParameter_range 5 p (by omega) _ _ _

/-- All five independently smoothed named nodes cover the target. -/
theorem arithmeticZeroDiagonalPolygon_named_cover (x : Y) :
    x ∈ Set.range T ∨ (∃ b, x ∈ Set.range (I b)) ∨ ∃ b, x ∈ Set.range (L b) := by
  obtain ⟨i, y, hy⟩ := PolygonVariableSmoothing.charts_cover Q 5 p (by omega) x
  have hx : x ∈ Set.range (c i) := ⟨y, hy⟩
  rcases polygonIndex_cases 1 i with rfl | ⟨b, rfl⟩ | ⟨a, b, rfl⟩
  · exact Or.inl ((arithmeticZeroDiagonalPolygonTerminalChart_range hπ data H m hj u hu).symm ▸ hx)
  · exact Or.inr (Or.inl ⟨b,
      (arithmeticZeroDiagonalPolygonInitialChart_range hπ data H m hj u hu b).symm ▸ hx⟩)
  · have ha : a = 0 := Fin.eq_zero a
    subst a
    exact Or.inr (Or.inr ⟨b,
      (arithmeticZeroDiagonalPolygonRetainedChart_range hπ data H m hj u hu b).symm ▸ hx⟩)

/-- Either orientation of an entire initial node preserves its full image. -/
theorem arithmeticZeroDiagonalPolygonInitialMap_range (b : Bool) :
    Set.range (C b) = Set.range (I b) := by
  cases b
  · simp only [arithmeticZeroDiagonalPolygonInitialMap, Bool.false_eq_true, ↓reduceIte,
      Category.id_comp]
  · let e := branchSwapIso Q ((arithmeticZeroDiagonalState hπ data H 0 hj u hu).initial m true)
    have he : Function.Surjective e.hom := e.hom.homeomorph.surjective
    change Set.range (I true ∘ e.hom) = _
    rw [Set.range_comp, he.range_eq, Set.image_univ]

/-- Either orientation of an entire retained node preserves its full image. -/
theorem arithmeticZeroDiagonalPolygonRetainedMap_range (b : Bool) :
    Set.range (G b) = Set.range (L b) := by
  cases b
  · simp only [arithmeticZeroDiagonalPolygonRetainedMap, Bool.false_eq_true, ↓reduceIte,
      Category.id_comp]
  · let e := branchSwapIso Q ((arithmeticZeroDiagonalState hπ data H 0 hj u hu).last m true)
    have he : Function.Surjective e.hom := e.hom.homeomorph.surjective
    change Set.range (L true ∘ e.hom) = _
    rw [Set.range_comp, he.range_eq, Set.image_univ]

/-- One constructed full target map for every actual corrected source label. -/
def arithmeticZeroDiagonalFactorRatioChartMap : (i : ArithmeticChartLabel 1) → A i ⟶ Y
  | .initial b => arithmeticZeroDiagonalFactorRatioInitialMap hπ data H m hj u hu b
  | .retained _ b => G b
  | .terminal => T
  | .infinity => arithmeticZeroDiagonalFactorRatioInfinityMap hπ data H m hj u hu

local notation "f" => arithmeticZeroDiagonalFactorRatioChartMap hπ data H m hj u hu

instance arithmeticZeroDiagonalFactorRatioChartMap_isOpenImmersion (i : ArithmeticChartLabel 1) :
    IsOpenImmersion (f i) := by
  cases i with
  | terminal =>
    unfold arithmeticZeroDiagonalFactorRatioChartMap arithmeticZeroDiagonalPolygonTerminalChart
    infer_instance
  | infinity =>
    exact arithmeticZeroDiagonalFactorRatioInfinityMap_isOpenImmersion hπ data H m hj u hu
  | initial b =>
    exact arithmeticZeroDiagonalFactorRatioInitialMap_isOpenImmersion hπ data H m hj u hu b
  | retained _ b =>
    exact arithmeticZeroDiagonalExteriorRetainedMap_isOpenImmersion hπ data H m hj u hu b

/-- The actual full source chart maps jointly cover every point of the independent target. -/
theorem arithmeticZeroDiagonalFactorRatioChartMap_cover (x : Y) :
    ∃ (i : ArithmeticChartLabel 1) (y : A i), f i y = x := by
  rcases arithmeticZeroDiagonalPolygon_named_cover hπ data H m hj u hu x with
    ⟨y, hy⟩ | ⟨b, hx⟩ | ⟨b, hx⟩
  · exact ⟨.terminal, y, hy⟩
  · rw [← arithmeticZeroDiagonalPolygonInitialMap_range hπ data H m hj u hu b] at hx
    obtain ⟨y, rfl⟩ := hx
    rcases arithmeticZeroDiagonalFactorRatioInitialInfinity_cover hπ data H m hj u hu b y with
      ⟨z, hz⟩ | ⟨z, hz⟩
    · exact ⟨.initial b, z, hz⟩
    · exact ⟨.infinity, z, hz⟩
  · rw [← arithmeticZeroDiagonalPolygonRetainedMap_range hπ data H m hj u hu b] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨.retained 0 b, y, hy⟩

end FLT.Mazur.WeierstrassDividedDepth
