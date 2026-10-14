/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitRetainedTensorDesc
public import FLT.Mazur.WeierstrassDividedAdjacentBranchCompatibility
import all FLT.Mazur.WeierstrassDividedPositiveSplitRetainedTensorDesc
import all FLT.Mazur.WeierstrassDividedPositiveSplitLocalMaps
import all FLT.Mazur.WeierstrassDividedPositiveSplitAtlasFamily

/-!
# Complete overlap compatibility for the strict retained-cycle tensor descents

Both local descents are the pullbacks of the actual fixed atlas family.
Their four proved branch restrictions give equality on the entire adjacent
fiber product, at every later common retained stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth) (j : Fin (s + 1))
local notation "K" => ResidueField R
variable (hj : j.val + 1 < s + 1)
  (r : ℕ) (hr : j.val + 2 + r ≤ n)
local notation "nextJ" => (Fin.mk (j.val + 1) hj : Fin (s + 1))
local notation "g" => adjacentRetainedOldGlobalTensorChart hπ data K
  j.val (by omega) r hr
local notation "gNext" => olderGlobalTensorChart hπ data K
  (j.val + 1) (by omega) r hr
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 5) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "d" => positiveSplitCycleRetainedTensorDesc hπ data D s hs hstart hk hp j F w
local notation "dNext" => positiveSplitCycleRetainedTensorDesc
  hπ data D s hs hstart hk hp nextJ F w

/-- The positive-start cyclic descents agree on the entire adjacent tensor intersection. -/
theorem positiveSplitCycleRetainedTensorDesc_compatible :
    Limits.pullback.fst g gNext ≫ d = Limits.pullback.snd g gNext ≫ dNext := by
  apply adjacentRetained_compatible_of_branch_restrictions hπ data D j.val
    (by omega) (by omega) (by omega) r hr (by omega) d dNext (by omega) (by omega)
    (Iff.mpr (residue_eq_zero_iff _) (WeierstrassDilatation.divided_constant_mem
      D (start + j.val + 2) (by omega) _ (Data.factor6 _)))
    (F ⟨j.val + 2, by omega⟩) (F ⟨2 * s + 4 - (j.val + 1), by omega⟩)
  · rw [positiveSplitCycleRetainedTensorDesc_first]
    exact positiveSplitCycleFirstLocalDesc_conic data D s hs hp j F w
  · rw [positiveSplitCycleRetainedTensorDesc_second]
    exact positiveSplitCycleSecondLocalDesc_conic data D s hs hp j F w
  · rw [positiveSplitCycleRetainedTensorDesc_first hπ data D s hs hstart hk hp nextJ F w]
    exact positiveSplitCycleFirstLocalDesc_line data D s hs hp nextJ F w
  · rw [positiveSplitCycleRetainedTensorDesc_second hπ data D s hs hstart hk hp nextJ F w]
    exact positiveSplitCycleSecondLocalDesc_line data D s hs hp nextJ F w

end FLT.Mazur.WeierstrassDividedDepth
