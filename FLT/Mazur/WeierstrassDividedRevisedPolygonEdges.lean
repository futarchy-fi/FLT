/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedPolygon
public import FLT.Mazur.WeierstrassDividedTwistedAtlas

/-!
# Both standard closing edges of the revised polygon

The target uses its changed terminal node exactly once. Each original retained
orientation gives the required full Laurent closing equation in that target.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
/-- The reversed left puncture becomes the complete incoming puncture after branch exchange. -/
@[reassoc] theorem revisedPolygon_inverseLeft_swap {S : Type} [CommRing S]
    (t : S) {Y : Scheme} (f : PolygonSmoothing.chart S t ⟶ Y) :
    ((edgeInversion S).hom ≫ leftBranchOpen S t) ≫ (branchSwapIso S t).hom ≫ f =
      precedingBranch S t ≫ f := by
  rw [Category.assoc, leftBranchOpen_branchSwapIso_assoc, precedingBranch, Category.assoc]

variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "N" => 2 * (j + 1) + 3
local notation "p" => arithmeticRevisedPolygonParameter data H m j hj u hu
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "σ" => arithmeticTerminalChangedSmoothing data H m j hj u hu
local notation "c" => arithmeticRevisedPolygonRetainedChart data H m j hj u hu
local notation "d" => arithmeticRevisedPolygonTerminalChart data H m j hj u hu
local notation "L" => arithmeticClosingRetainedBoundary data H m
local notation "O" => twistedRetainedOrientation data H m

/-- The last first-arm node and the terminal have their precise cyclic edge. -/
@[reassoc] theorem arithmeticRevisedPolygon_closing_false :
    L ≫ c ⟨j, by omega⟩ false = rightBranchOpen Q σ ≫ d := by
  have he : leftBranchOpen Q τ ≫ c ⟨j, by omega⟩ false =
      precedingBranch Q σ ≫ d :=
    PolygonVariableSmoothing.chartWithParameter_overlap Q N p (by omega) _ 0
      (retainedPolygonIndex_false_terminal j) τ σ _ _
  rw [arithmeticClosingRetainedBoundary, Category.assoc, he, precedingBranch,
    Category.assoc]
  exact (edgeInversion Q).inv_hom_id_assoc _

/-- The opposite last node uses the other puncture of the same changed terminal. -/
@[reassoc] theorem arithmeticRevisedPolygon_closing_true :
    L ≫ (O true).hom ≫ c ⟨j, by omega⟩ true = leftBranchOpen Q σ ≫ d := by
  have he : leftBranchOpen Q σ ≫ d = precedingBranch Q τ ≫ c ⟨j, by omega⟩ true :=
    PolygonVariableSmoothing.chartWithParameter_overlap Q N p (by omega) 0 _
      (retainedPolygonIndex_true_terminal j) σ τ _ _
  exact (revisedPolygon_inverseLeft_swap τ (c ⟨j, by omega⟩ true)).trans he.symm

/-- Both closing equations retain the original retained orientation and complete punctures. -/
@[reassoc] theorem arithmeticRevisedPolygon_closing (b : Bool) :
    L ≫ (O b).hom ≫ c ⟨j, by omega⟩ b =
      (if b then leftBranchOpen Q σ else rightBranchOpen Q σ) ≫ d := by
  cases b
  · simp only [twistedRetainedOrientation, Bool.false_eq_true, ↓reduceIte, Iso.refl_hom,
      Category.id_comp]
    exact arithmeticRevisedPolygon_closing_false data H m j hj u hu
  · exact arithmeticRevisedPolygon_closing_true data H m j hj u hu

end FLT.Mazur.WeierstrassDividedDepth
