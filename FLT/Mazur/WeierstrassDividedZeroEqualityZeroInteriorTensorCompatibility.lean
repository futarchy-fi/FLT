/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityInteriorTensorDesc
public import FLT.Mazur.WeierstrassDividedAdjacentZeroBranchCompatibility
public import FLT.Mazur.WeierstrassDividedZeroEqualityZeroTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityZeroTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositiveAttachmentMaps
import all FLT.Mazur.WeierstrassDividedZeroEqualityInteriorTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityInteriorLocalMaps
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositiveAtlasFamily

/-!
# Complete initial/interior overlap for equality-cycle tensor descents

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
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth) (hs2 : 1 < s)
local notation "K" => ResidueField R
variable (r : ℕ) (hr : 0 + 2 + r ≤ n)
local notation "firstJ" => (Fin.mk 0 (by omega) : Fin (s - 1))
local notation "g" => adjacentRetainedOldGlobalTensorChart hπ data K 0 (by omega) r hr
local notation "gNext" => olderGlobalTensorChart hπ data K (0 + 1) (by omega) r hr
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 2) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "d" => zeroEqualityPositiveCycleZeroTensorDesc
  hπ data s hs D hstart hk hp (by omega) F w
local notation "dNext" => zeroEqualityCycleInteriorTensorDesc
  hπ data D s hs hstart hk hp (by omega) firstJ F w

include hs2 in
/-- The original zero and first positive descents agree on the complete tensor intersection. -/
theorem zeroEqualityCycleZeroInteriorTensorDesc_compatible :
    Limits.pullback.fst g gNext ≫ d = Limits.pullback.snd g gNext ≫ dNext := by
  apply adjacentZero_compatible_of_branch_restrictions hπ data D 0
    (by omega) (by omega) (by omega) r hr (by omega) d dNext (by omega) (by omega)
    (Iff.mpr (residue_eq_zero_iff _) (WeierstrassDilatation.divided_constant_mem
      D (start + 0 + 2) (by omega) _ (Data.factor6 _)))
    (F 1) (F ⟨2 * s + 1, by omega⟩)
  · simp only [Category.assoc]
    rw [zeroEqualityPositiveCycleZeroTensorDesc_first]
    exact zeroEqualityPositiveCycleFirstAttachmentDesc_conic data D s hs hk (by omega) F w
  · simp only [Category.assoc]
    rw [zeroEqualityPositiveCycleZeroTensorDesc_second]
    exact zeroEqualityPositiveCycleSecondAttachmentDesc_conic
      data D s hs hk (by omega) F w
  · rw [zeroEqualityCycleInteriorTensorDesc_first hπ data D s hs hstart hk hp (by omega) firstJ F w]
    exact zeroEqualityCycleInteriorFirstLocalDesc_line data D s hs hstart hk firstJ F w
  · rw [zeroEqualityCycleInteriorTensorDesc_second
      hπ data D s hs hstart hk hp (by omega) firstJ F w]
    exact zeroEqualityCycleInteriorSecondLocalDesc_line data D s hs hstart hk firstJ F w

end FLT.Mazur.WeierstrassDividedDepth
