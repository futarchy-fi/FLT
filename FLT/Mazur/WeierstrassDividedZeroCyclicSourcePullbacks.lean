/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclicGlobalIso
public import FLT.Mazur.PolygonVariableSmoothingEdgeIntersection

/-!
# The five full source edges are scheme-theoretic intersections

Transport the independent standard atlas fiber products through the full node,
puncture and global isomorphisms. All original edge substitutions are retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "S" => arithmeticZeroCyclicSeed hπ data H hj u hu
local notation "D" => arithmeticZeroCyclicDiagonal hπ data H hj u hu
local notation "t" => arithmeticZeroCyclicStandardParameter hπ data H hj u hu m
local notation "N" => arithmeticZeroCyclicNodeIso hπ data H hj u hu m
local notation "P" => arithmeticZeroCyclicPunctureIso hπ data H hj u hu m
local notation "F" => arithmeticZeroCyclicGlobalIso hπ data H m hj u hu
local notation "c" => arithmeticZeroCyclicSourceChart hπ data H m hj u hu
local notation "e" => zeroCyclicIndex

/-- Every standard-indexed original full cyclic edge is its two-node scheme intersection. -/
theorem arithmeticZeroCyclicSourceChart_indexed_isPullback (i : Fin 5) :
    IsPullback (leftBranchOpen Q ((S).parameter m (e i)))
      ((punctureSpecIso ((S).edge m (e i))).hom ≫
        rightBranchOpen Q ((S).parameter m (e ((finRotate 5).symm i))))
      (c (e i)) (c (e ((finRotate 5).symm i))) := by
  have hn : i ≠ (finRotate 5).symm i := by fin_cases i <;> decide
  have hr : (finRotate 5).symm ((finRotate 5).symm i) ≠ i := by fin_cases i <;> decide
  have h := PolygonVariableSmoothing.edge_isPullback Q 5 t (by decide) i
    ((finRotate 5).symm i) rfl hn hr
  apply h.of_iso' (P (e i) true) (N (e i)) (N (e ((finRotate 5).symm i))) F
  · simpa only [punctureOpen_true, arithmeticZeroCyclicStandardParameter] using
      (arithmeticZeroCyclicNodeIso_puncture hπ data H hj u hu m (e i) true).symm
  · simp only [precedingBranch, Category.assoc, arithmeticZeroCyclicStandardParameter]
    have hp := arithmeticZeroCyclicNodeIso_puncture hπ data H hj u hu m
      (e ((finRotate 5).symm i)) false
    rw [punctureOpen_false, punctureOpen_false] at hp
    rw [hp, arithmeticZeroCyclicPunctureIso_edge_assoc]
    have he := congrArg (fun j ↦ (P j false).hom) (zeroCyclicIndex_preceding i)
    rw [he]
  · exact (arithmeticZeroCyclicGlobalIso_chart hπ data H m hj u hu i).symm
  · exact (arithmeticZeroCyclicGlobalIso_chart hπ data H m hj u hu
      ((finRotate 5).symm i)).symm

/-- Each exact full seed edge, including both terminal attachments, is a genuine pullback. -/
theorem arithmeticZeroCyclicSourceChart_edge_isPullback (i : ZeroCyclicVertex) :
    IsPullback (leftBranchOpen Q ((S).parameter m i))
      ((punctureSpecIso ((S).edge m i)).hom ≫
        rightBranchOpen Q ((S).parameter m (zeroCyclicSuccessor i)))
      (c i) (c (zeroCyclicSuccessor i)) := by
  rcases i with _ | (_ | _) | (_ | _)
  · exact arithmeticZeroCyclicSourceChart_indexed_isPullback hπ data H m hj u hu 0
  · exact arithmeticZeroCyclicSourceChart_indexed_isPullback hπ data H m hj u hu 1
  · exact arithmeticZeroCyclicSourceChart_indexed_isPullback hπ data H m hj u hu 4
  · exact arithmeticZeroCyclicSourceChart_indexed_isPullback hπ data H m hj u hu 2
  · exact arithmeticZeroCyclicSourceChart_indexed_isPullback hπ data H m hj u hu 3

end FLT.Mazur.WeierstrassDividedDepth
