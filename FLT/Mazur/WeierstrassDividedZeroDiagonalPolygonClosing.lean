/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalPolygon
public import FLT.Mazur.WeierstrassDividedZeroDiagonalAtlasOverlaps
public import FLT.Mazur.WeierstrassDividedRevisedPolygonEdges

/-!
# Both complete diagonal closing branches in the independent target

The two retained nodes and the common terminal retain their distinct actual
smoothings. Their entire Laurent attachments satisfy the original orientations.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "p" => arithmeticZeroDiagonalPolygonParameter hπ data H hj u hu m
local notation "s" => PolygonArithmeticSimultaneous.State.last D m
local notation "t" => PolygonArithmeticSimultaneous.State.terminal D m
local notation "c" => arithmeticZeroDiagonalPolygonRetainedChart hπ data H m hj u hu
local notation "d" => arithmeticZeroDiagonalPolygonTerminalChart hπ data H m hj u hu

/-- The full retained comparison uses its original orientation on its actual diagonal node. -/
def arithmeticZeroDiagonalPolygonRetainedMap (b : Bool) :
    PolygonSmoothing.chart Q (s b) ⟶ arithmeticZeroDiagonalPolygon hπ data H m hj u hu :=
  (if b then (branchSwapIso Q (s b)).hom else 𝟙 _) ≫ c b

local notation "f" => arithmeticZeroDiagonalPolygonRetainedMap hπ data H m hj u hu

/-- Both entire closing punctures land on the same terminal of the independent target. -/
@[reassoc] theorem arithmeticZeroDiagonalPolygon_closing (b : Bool) :
    ((edgeInversion Q).hom ≫ leftBranchOpen Q (s b)) ≫ f b =
      punctureOpen t b ≫ d := by
  cases b
  · have he : leftBranchOpen Q (s false) ≫ c false = precedingBranch Q t ≫ d :=
      PolygonVariableSmoothing.chartWithParameter_overlap Q 5 p (by omega) _ 0
        (retainedPolygonIndex_false_terminal 0) _ _ _ _
    simp only [arithmeticZeroDiagonalPolygonRetainedMap, Bool.false_eq_true, ↓reduceIte,
      Category.id_comp, punctureOpen_false, Category.assoc]
    rw [he, precedingBranch, Category.assoc]
    exact (edgeInversion Q).inv_hom_id_assoc _
  · have he : leftBranchOpen Q t ≫ d = precedingBranch Q (s true) ≫ c true :=
      PolygonVariableSmoothing.chartWithParameter_overlap Q 5 p (by omega) 0 _
        (retainedPolygonIndex_true_terminal 0) _ _ _ _
    rw [punctureOpen_true]
    exact (revisedPolygon_inverseLeft_swap (s true) (c true)).trans he.symm

instance arithmeticZeroDiagonalTerminalPuncture_isOpenImmersion (b : Bool) :
    IsOpenImmersion (punctureOpen t b) := by
  cases b
  · rw [punctureOpen_false]
    infer_instance
  · rw [punctureOpen_true]
    infer_instance

/-- The complete actual diagonal closing attachment maps into the independent polygon. -/
def arithmeticZeroDiagonalClosingMap (b : Bool) :
    pushout ((edgeInversion Q).hom ≫ leftBranchOpen Q (s b)) (punctureOpen t b) ⟶
      arithmeticZeroDiagonalPolygon hπ data H m hj u hu :=
  pushout.desc (f b) d (arithmeticZeroDiagonalPolygon_closing hπ data H m hj u hu b)

/-- The entire retained node of the attachment keeps its explicit comparison map. -/
@[reassoc] theorem arithmeticZeroDiagonalClosingMap_retained (b : Bool) :
    pushout.inl ((edgeInversion Q).hom ≫ leftBranchOpen Q (s b)) (punctureOpen t b) ≫
      arithmeticZeroDiagonalClosingMap hπ data H m hj u hu b = f b :=
  pushout.inl_desc _ _ _

/-- Both complete attachments use the same full terminal map. -/
@[reassoc] theorem arithmeticZeroDiagonalClosingMap_terminal (b : Bool) :
    pushout.inr ((edgeInversion Q).hom ≫ leftBranchOpen Q (s b)) (punctureOpen t b) ≫
      arithmeticZeroDiagonalClosingMap hπ data H m hj u hu b = d :=
  pushout.inr_desc _ _ _

end FLT.Mazur.WeierstrassDividedDepth
