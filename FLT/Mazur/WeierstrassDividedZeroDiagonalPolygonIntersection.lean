/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalPolygonClosing
public import FLT.Mazur.WeierstrassDividedRevisedClosingIntersection

/-!
# Full intersections of the diagonal closing nodes

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

local notation "f" => arithmeticZeroDiagonalPolygonRetainedMap hπ data H m hj u hu

/-- Each diagonal closing edge is the entire intersection of its full target nodes. -/
theorem arithmeticZeroDiagonalPolygon_closing_isPullback (b : Bool) :
    IsPullback ((edgeInversion Q).hom ≫ leftBranchOpen Q (s b)) (punctureOpen t b)
      (f b) d := by
  cases b
  · have hn : (finRotate 5).symm 0 ≠ retainedPolygonIndex 1 0 false := by
      rw [retainedPolygonIndex_true_terminal 0]
      exact revisedPolygon_last_labels_ne 0
    have he := PolygonVariableSmoothing.identifiedEdge_isPullback Q 5 p (by omega)
      (retainedPolygonIndex 1 0 false) 0 (retainedPolygonIndex_false_terminal 0)
      (retainedPolygonIndex_ne_terminal 1 0 false) hn (s false) t
      (arithmeticZeroDiagonalPolygonParameter_retained hπ data H hj u hu m 0 false).symm rfl
    simpa only [arithmeticZeroDiagonalPolygonRetainedMap, Bool.false_eq_true, ↓reduceIte,
      Category.id_comp, punctureOpen_false] using
      PolygonVariableSmoothing.inverseEdge_isPullback Q (s false) t (c false) d he
  · have hn : (finRotate 5).symm (retainedPolygonIndex 1 0 true) ≠ 0 := by
      intro he
      exact revisedPolygon_last_labels_ne 0
        ((finRotate 5).symm.injective (he.trans (retainedPolygonIndex_false_terminal 0).symm))
    have he := PolygonVariableSmoothing.identifiedEdge_isPullback Q 5 p (by omega)
      0 (retainedPolygonIndex 1 0 true) (retainedPolygonIndex_true_terminal 0)
      (retainedPolygonIndex_ne_terminal 1 0 true).symm hn t (s true) rfl
      (arithmeticZeroDiagonalPolygonParameter_retained hπ data H hj u hu m 0 true).symm
    simpa only [arithmeticZeroDiagonalPolygonRetainedMap, ↓reduceIte, punctureOpen_true] using
      PolygonVariableSmoothing.swappedEdge_isPullback Q (s true) t (c true) d he.flip

end FLT.Mazur.WeierstrassDividedDepth
