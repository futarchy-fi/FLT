/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityTerminalTensorDesc
public import FLT.Mazur.WeierstrassDividedAdjacentZeroParameterBranchCompatibility
public import FLT.Mazur.WeierstrassDividedZeroEqualityZeroTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityZeroTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositiveAttachmentMaps
import all FLT.Mazur.WeierstrassDividedZeroEqualityTerminalTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityTerminalLocalMaps
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositiveAtlasFamily

/-!
# The depth-one initial/terminal overlap with its actual conic constant

The oldest split conic meets the terminal horizontal branches on the two
original punctures. No vanishing of the terminal divided constant is used.
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
  (D : SplitNodeDepth W π depth) (hs : 1 + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + 1 + 1) ≤ depth)
  (hp : 2 * (start + 1 + 1) = depth)
local notation "K" => ResidueField R
variable (r : ℕ) (hr : 0 + 2 + r ≤ n)
local notation "g" => adjacentRetainedOldGlobalTensorChart hπ data K 0 (by omega) r hr
local notation "gNext" => olderGlobalTensorChart hπ data K (0 + 1) (by omega) r hr
variable {Y : Scheme.{u}}
  (F : Fin (2 * 1 + 2) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "d" => zeroEqualityPositiveCycleZeroTensorDesc
  hπ data 1 hs D hstart hk hp (by omega) F w
local notation "dNext" => zeroEqualityCycleTerminalTensorDesc hπ data D 1 hs hk hp (by omega) F w

/-- The original zero and first positive descents agree on the complete tensor intersection. -/
theorem zeroEqualityCycleOneZeroTerminalTensorDesc_compatible :
    Limits.pullback.fst g gNext ≫ d = Limits.pullback.snd g gNext ≫ dNext := by
  apply adjacentZero_compatible_of_parameter_branch_restrictions hπ data D 0
    (by omega) (by omega) (by omega) r hr (by omega) d dNext (by omega) (by omega)
    (F 1) (F ⟨2 * 1 + 1, by omega⟩)
  · simp only [Category.assoc]
    rw [zeroEqualityPositiveCycleZeroTensorDesc_first]
    exact zeroEqualityPositiveCycleFirstAttachmentDesc_conic data D 1 hs hk (by omega) F w
  · simp only [Category.assoc]
    rw [zeroEqualityPositiveCycleZeroTensorDesc_second]
    exact zeroEqualityPositiveCycleSecondAttachmentDesc_conic data D 1 hs hk (by omega) F w
  · rw [zeroEqualityCycleTerminalTensorDesc_first hπ data D 1 hs hk hp (by omega) F w]
    exact zeroEqualityCycleTerminalFirstDesc_line data D 1 hs hk hp F w
  · rw [zeroEqualityCycleTerminalTensorDesc_second hπ data D 1 hs hk hp (by omega) F w]
    exact zeroEqualityCycleTerminalSecondDesc_line data D 1 hs hk hp F w (by omega)

end FLT.Mazur.WeierstrassDividedDepth
