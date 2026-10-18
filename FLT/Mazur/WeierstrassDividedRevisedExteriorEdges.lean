/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedPolygonEdges

/-!
# Full exterior edges in the independently constructed revised polygon

The initial and retained labels retain their complete Laurent overlaps.
Both arm orientations use the same cyclic diagram as the closing pairs.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "N" => 2 * (j + 1) + 3
local notation "p" => arithmeticRevisedPolygonParameter data H m j hj u hu
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "c" => arithmeticRevisedPolygonRetainedChart data H m j hj u hu
local notation "d" => arithmeticRevisedPolygonInitialChart data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m

/-- The full oriented retained nodes satisfy every original consecutive edge equation. -/
@[reassoc] theorem arithmeticRevisedPolygon_adjacent
    (a : ℕ) (ha : a + 1 < j + 1) (b : Bool) :
    leftBranchOpen Q τ ≫ (O b).hom ≫ c ⟨a, by omega⟩ b =
      precedingBranch Q τ ≫ (O b).hom ≫ c ⟨a + 1, ha⟩ b := by
  cases b
  · simp only [twistedRetainedOrientation, Bool.false_eq_true, ↓reduceIte,
      Iso.refl_hom, Category.id_comp]
    exact PolygonVariableSmoothing.chartWithParameter_overlap Q N p (by omega) _ _
      (retainedPolygonIndex_false_preceding (j + 1) a ha) τ τ _ _
  · simp only [twistedRetainedOrientation, ↓reduceIte, ← Category.assoc,
      leftBranchOpen_branchSwapIso_preceding, precedingBranch_branchSwapIso]
    have hi : (edgeInversion Q).inv = (edgeInversion Q).hom := rfl
    rw [hi, Category.assoc, Category.assoc]
    congr 1
    exact (PolygonVariableSmoothing.chartWithParameter_overlap Q N p (by omega) _ _
      (retainedPolygonIndex_true_preceding (j + 1) a ha) τ τ _ _).symm

/-- Both initial labels meet their first retained node on the entire standard edge. -/
@[reassoc] theorem arithmeticRevisedPolygon_initial_retained (b : Bool) :
    leftBranchOpen Q τ ≫ (O b).hom ≫ d b =
      precedingBranch Q τ ≫ (O b).hom ≫ c ⟨0, Nat.zero_lt_succ j⟩ b := by
  cases b
  · simp only [twistedRetainedOrientation, Bool.false_eq_true, ↓reduceIte,
      Iso.refl_hom, Category.id_comp]
    exact PolygonVariableSmoothing.chartWithParameter_overlap Q N p (by omega) _ _
      (initialPolygonIndex_false_retained (j + 1) (Nat.zero_lt_succ j)) τ τ _ _
  · simp only [twistedRetainedOrientation, ↓reduceIte, ← Category.assoc,
      leftBranchOpen_branchSwapIso_preceding, precedingBranch_branchSwapIso]
    have hi : (edgeInversion Q).inv = (edgeInversion Q).hom := rfl
    rw [hi, Category.assoc, Category.assoc]
    congr 1
    exact (PolygonVariableSmoothing.chartWithParameter_overlap Q N p (by omega) _ _
      (initialPolygonIndex_true_retained (j + 1) (Nat.zero_lt_succ j)) τ τ _ _).symm

/-- The two initial nodes meet along the full cyclic infinity edge. -/
@[reassoc] theorem arithmeticRevisedPolygon_initial_initial :
    leftBranchOpen Q τ ≫ d true = precedingBranch Q τ ≫ d false :=
  PolygonVariableSmoothing.chartWithParameter_overlap Q N p (by omega) _ _
    (initialPolygonIndex_preceding (j + 1)) τ τ _ _

/-- In the original opposite orientation, the infinity edge uses reciprocal parameters. -/
@[reassoc] theorem arithmeticRevisedPolygon_infinity :
    rightBranchOpen Q τ ≫ (O true).hom ≫ d true =
      (edgeInversion Q).hom ≫ rightBranchOpen Q τ ≫ d false := by
  rw [twistedRetainedOrientation]
  simp only [↓reduceIte, rightBranchOpen_branchSwapIso_assoc]
  exact arithmeticRevisedPolygon_initial_initial data H m j hj u hu

end FLT.Mazur.WeierstrassDividedDepth
