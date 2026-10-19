/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclicSourceCharts
public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedPairBase
public import FLT.Mazur.PolygonSmoothingBranchSwapBase

/-!
# The five original cyclic source charts over their arithmetic base

Both entire initial charts and both reflected nodes preserve the original
coefficient projection. The terminal remains the one common original chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticZeroDiagonalAtlasChart
  arithmeticZeroInfinityNormalizedFullComparison
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "r" => rightBranchOpen Q τ
local notation "r'" => Iso.hom (edgeInversion Q) ≫ r
local notation "U" => arithmeticZeroInfinityNormalizedFullUnion hπ data H m hj u hu
local notation "F" => arithmeticZeroInfinityNormalizedFullComparison hπ data H m hj u hu
local notation "c" => arithmeticZeroDiagonalAtlasChart hπ data H m hj u hu
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "S" => arithmeticZeroCyclicSeed hπ data H hj u hu
local notation "X" => simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu

local notation "q" => arithmeticZeroDiagonalSourceToBase hπ data H m hj u hu
local notation "a" => arithmeticZeroCyclicInitialChart hπ data H m hj u hu

/-- Every unreflected initial node retains the full original arithmetic base. -/
@[reassoc] theorem arithmeticZeroCyclicInitialChart_base (b : Bool) :
    a b ≫ q = chartStructure Q τ := by
  have hf : (F).inv ≫ (U).ι ≫ q =
      arithmeticZeroInfinityNormalizedTargetToBase data H m := by
    rw [← arithmeticZeroInfinityNormalizedFullComparison_base hπ data H m hj u hu,
      Iso.inv_hom_id_assoc]
  cases b <;> simp only [arithmeticZeroCyclicInitialChart, Bool.false_eq_true,
    ↓reduceIte, Category.assoc, hf]
  · exact arithmeticZeroInfinityNormalizedTargetToBase_first data H m
  · exact arithmeticZeroInfinityNormalizedTargetToBase_opposite data H m

/-- Each of the five full cyclic source nodes lies over its actual coefficient base. -/
@[reassoc] theorem arithmeticZeroCyclicSourceChart_base (i : ZeroCyclicVertex) :
    arithmeticZeroCyclicSourceChart hπ data H m hj u hu i ≫ q =
      chartStructure Q ((S).parameter m i) := by
  rcases i with _ | (_ | _) | (_ | _)
  · exact arithmeticZeroDiagonalAtlas_terminal_base hπ data H m hj u hu
  · exact arithmeticZeroDiagonalAtlas_retained_base hπ data H m hj u hu false
  · dsimp only [arithmeticZeroCyclicSourceChart]
    rw [Category.assoc, arithmeticZeroDiagonalAtlas_retained_base, branchSwapIso_base]
    rfl
  · exact arithmeticZeroCyclicInitialChart_base hπ data H m hj u hu false
  · dsimp only [arithmeticZeroCyclicSourceChart]
    rw [Category.assoc, arithmeticZeroCyclicInitialChart_base, branchSwapIso_base]
    rfl

end FLT.Mazur.WeierstrassDividedDepth
