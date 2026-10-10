/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveTensorDesc
public import FLT.Mazur.WeierstrassDividedAdjacentBranchCompatibility
import all FLT.Mazur.WeierstrassDividedZeroCyclePositiveTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroCycleLocalMaps
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasFamily

/-!
# Complete overlap compatibility for the positive cyclic tensor descents

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
  (hstart : start = 0) (hp : 2 * (start + s + 1) < depth) (j : Fin s)
local notation "K" => ResidueField R
variable (hj : j.val + 1 < s)
  (r : ℕ) (hr : (j.val + 1) + 2 + r ≤ n)
local notation "nextJ" => (Fin.mk (j.val + 1) hj : Fin s)
local notation "g" => adjacentRetainedOldGlobalTensorChart hπ data K
  (j.val + 1) (by omega) r hr
local notation "gNext" => olderGlobalTensorChart hπ data K
  ((j.val + 1) + 1) (by omega) r hr
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "d" => zeroSplitCyclePositiveTensorDesc hπ data s hs j D hstart hp F w
local notation "dNext" => zeroSplitCyclePositiveTensorDesc hπ data s hs nextJ D hstart hp F w

/-- The original positive cyclic descents agree on the entire adjacent tensor intersection. -/
theorem zeroSplitCyclePositiveTensorDesc_compatible :
    Limits.pullback.fst g gNext ≫ d = Limits.pullback.snd g gNext ≫ dNext := by
  apply adjacentRetained_compatible_of_branch_restrictions hπ data D (j.val + 1)
    (by omega) (by omega) (by omega) r hr (by omega) d dNext (by omega) (by omega)
    (Iff.mpr (residue_eq_zero_iff _) (WeierstrassDilatation.divided_constant_mem
      D (start + (j.val + 1) + 2) (by omega) _ (Data.factor6 _)))
    (F ⟨j.val + 2, by omega⟩) (F ⟨2 * s + 2 - (j.val + 1), by omega⟩)
  · rw [zeroSplitCyclePositiveTensorDesc_first]
    exact zeroSplitCycleFirstLocalDesc_conic data D s hs hstart hp j F w
  · rw [zeroSplitCyclePositiveTensorDesc_second]
    exact zeroSplitCycleSecondLocalDesc_conic data D s hs hstart hp j F w
  · rw [zeroSplitCyclePositiveTensorDesc_first hπ data s hs nextJ D hstart hp F w]
    exact zeroSplitCycleFirstLocalDesc_line data D s hs hstart hp nextJ F w
  · rw [zeroSplitCyclePositiveTensorDesc_second hπ data s hs nextJ D hstart hp F w]
    exact zeroSplitCycleSecondLocalDesc_line data D s hs hstart hp nextJ F w

end FLT.Mazur.WeierstrassDividedDepth
