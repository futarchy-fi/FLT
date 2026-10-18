/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalFactorRatio
public import FLT.Mazur.WeierstrassDividedZeroDiagonalPolygonClosing

/-!
# All exterior edges of the actual variable-smoothing diagonal polygon

Both oriented initial-to-retained edges and the common infinity edge use
independent accumulated smoothings and full Laurent coordinates.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticZeroDiagonalState
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "p" => arithmeticZeroDiagonalPolygonParameter hπ data H hj u hu m
local notation "s" => PolygonArithmeticSimultaneous.State.initial D m
local notation "t" => PolygonArithmeticSimultaneous.State.last D m
local notation "c" => arithmeticZeroDiagonalPolygonInitialChart hπ data H m hj u hu
local notation "d" => arithmeticZeroDiagonalPolygonRetainedChart hπ data H m hj u hu
local notation "C" => arithmeticZeroDiagonalPolygonInitialMap hπ data H m hj u hu
local notation "F" => arithmeticZeroDiagonalPolygonRetainedMap hπ data H m hj u hu

/-- Both initial nodes meet their retained node along the complete oriented edge. -/
@[reassoc] theorem arithmeticZeroDiagonalPolygon_initial_retained (b : Bool) :
    leftBranchOpen Q (s b) ≫ C b =
      (edgeInversion Q).hom ≫ rightBranchOpen Q (t b) ≫ F b := by
  cases b
  · have he : leftBranchOpen Q (s false) ≫ c false =
        precedingBranch Q (t false) ≫ d false :=
      PolygonVariableSmoothing.chartWithParameter_overlap Q 5 p (by omega) _ _
        (initialPolygonIndex_false_retained 1 (by omega)) _ _ _ _
    simpa only [arithmeticZeroDiagonalPolygonInitialMap,
      arithmeticZeroDiagonalPolygonRetainedMap, Bool.false_eq_true, ↓reduceIte,
      Category.id_comp, precedingBranch, Category.assoc] using he
  · have he : leftBranchOpen Q (t true) ≫ d true =
        precedingBranch Q (s true) ≫ c true :=
      PolygonVariableSmoothing.chartWithParameter_overlap Q 5 p (by omega) _ _
        (initialPolygonIndex_true_retained 1 (by omega)) _ _ _ _
    simp only [arithmeticZeroDiagonalPolygonInitialMap,
      arithmeticZeroDiagonalPolygonRetainedMap, ↓reduceIte, ← Category.assoc,
      leftBranchOpen_branchSwapIso_preceding, rightBranchOpen_branchSwapIso]
    have hi : (edgeInversion Q).inv = (edgeInversion Q).hom := rfl
    rw [hi, Category.assoc, Category.assoc]
    exact congrArg ((edgeInversion Q).hom ≫ ·) he.symm

/-- The two independently smoothed initial nodes share the full infinity edge. -/
@[reassoc] theorem arithmeticZeroDiagonalPolygon_initial_initial :
    leftBranchOpen Q (s true) ≫ c true =
      precedingBranch Q (s false) ≫ c false :=
  PolygonVariableSmoothing.chartWithParameter_overlap Q 5 p (by omega) _ _
    (initialPolygonIndex_preceding 1) _ _ _ _

/-- The original opposite orientation identifies the entire reciprocal infinity puncture. -/
@[reassoc] theorem arithmeticZeroDiagonalPolygon_infinity :
    rightBranchOpen Q (s true) ≫ C true =
      (edgeInversion Q).hom ≫ rightBranchOpen Q (s false) ≫ C false := by
  simp only [arithmeticZeroDiagonalPolygonInitialMap, Bool.false_eq_true, ↓reduceIte,
    Category.id_comp, rightBranchOpen_branchSwapIso_assoc]
  exact arithmeticZeroDiagonalPolygon_initial_initial hπ data H m hj u hu

instance arithmeticZeroDiagonalExteriorRetainedMap_isOpenImmersion (b : Bool) :
    IsOpenImmersion (F b) := by
  unfold arithmeticZeroDiagonalPolygonRetainedMap
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Category.id_comp] <;> infer_instance

end FLT.Mazur.WeierstrassDividedDepth
