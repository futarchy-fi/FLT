/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveTensorDesc
public import FLT.Mazur.WeierstrassDividedAdjacentZeroBranchCompatibility
public import FLT.Mazur.WeierstrassDividedZeroCycleZeroTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroCycleZeroTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroCycleAttachmentMaps
import all FLT.Mazur.WeierstrassDividedZeroCyclePositiveTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroCycleLocalMaps
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasFamily

/-!
# Complete overlap compatibility between zero and positive cyclic tensor descents

The full oldest node restrictions and the first positive node restrictions
agree on the two original punctures, hence on the whole scheme intersection.
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
  (hstart : start = 0) (hp : 2 * (start + s + 1) < depth) (hs0 : 0 < s)
local notation "K" => ResidueField R
variable (r : ℕ) (hr : 0 + 2 + r ≤ n)
local notation "firstJ" => (Fin.mk 0 hs0 : Fin s)
local notation "g" => adjacentRetainedOldGlobalTensorChart hπ data K 0 (by omega) r hr
local notation "gNext" => olderGlobalTensorChart hπ data K (0 + 1) (by omega) r hr
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "d" => zeroSplitCycleZeroTensorDesc hπ data s hs D hstart hp F w
local notation "dNext" => zeroSplitCyclePositiveTensorDesc hπ data s hs firstJ D hstart hp F w

/-- The original zero and first positive descents agree on the complete tensor intersection. -/
theorem zeroSplitCycleZeroPositiveTensorDesc_compatible :
    Limits.pullback.fst g gNext ≫ d = Limits.pullback.snd g gNext ≫ dNext := by
  apply adjacentZero_compatible_of_branch_restrictions hπ data D 0
    (by omega) (by omega) (by omega) r hr (by omega) d dNext (by omega) (by omega)
    (Iff.mpr (residue_eq_zero_iff _) (WeierstrassDilatation.divided_constant_mem
      D (start + 0 + 2) (by omega) _ (Data.factor6 _)))
    (F 1) (F ⟨2 * s + 2, by omega⟩)
  · simp only [Category.assoc]
    rw [zeroSplitCycleZeroTensorDesc_first]
    exact zeroSplitCycleFirstAttachmentDesc_conic data D s hs hp F w
  · simp only [Category.assoc]
    rw [zeroSplitCycleZeroTensorDesc_second]
    exact zeroSplitCycleSecondAttachmentDesc_conic data D s hs hp F w
  · rw [zeroSplitCyclePositiveTensorDesc_first hπ data s hs firstJ D hstart hp F w]
    exact zeroSplitCycleFirstLocalDesc_line data D s hs hstart hp firstJ F w
  · rw [zeroSplitCyclePositiveTensorDesc_second hπ data s hs firstJ D hstart hp F w]
    exact zeroSplitCycleSecondLocalDesc_line data D s hs hstart hp firstJ F w

end FLT.Mazur.WeierstrassDividedDepth
