/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityGlobalNodeRestrictions
public import FLT.Mazur.WeierstrassDividedZeroEqualityAttachmentBranches
public import FLT.Mazur.WeierstrassDividedZeroEqualityTerminalLineBranches
import all FLT.Mazur.WeierstrassDividedZeroEqualityGlobalNodeRestrictions
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositiveAtlasFamily
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositiveAtlasDescent
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositiveAttachmentMaps
import all FLT.Mazur.WeierstrassDividedZeroEqualityTerminalLocalMaps

/-!
# Global equality descent on the attachment and terminal chain charts

The oldest conic charts and the final horizontal charts recover their family
members with the original orientation and arbitrary terminal conic constant.
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
  (hp : 2 * (start + s + 1) = depth) (hpos : 0 < s)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 2) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "K" => ResidueField R
local notation "d" => zeroEqualityPositiveCycleGlobalDesc hπ data D s hs hstart hk hp hpos F w

local notation "Z" => zeroEqualityCycleComponent hπ data D s hs hstart hk hp

/-- The oldest first conic chart recovers its prescribed family member. -/
@[reassoc] theorem zeroEqualityPositiveCycleGlobalDesc_attachment_first_chart :
    ProjectiveLine.right K ≫ (Z 1).left ≫ d = ProjectiveLine.right K ≫ F 1 := by
  rw [zeroEqualityCycleComponent_first_attachment_conic_assoc hπ data D s hs hstart
    hk hp hpos, zeroEqualityPositiveCycleGlobalDesc_attachment_first,
    zeroEqualityPositiveCycleFirstAttachmentDesc_conic]

/-- The opposite oldest conic chart keeps the original second-chain orientation. -/
@[reassoc] theorem zeroEqualityPositiveCycleGlobalDesc_attachment_second_chart :
    ProjectiveLine.left K ≫ (Z ⟨2 * s + 1, by omega⟩).left ≫ d =
      ProjectiveLine.left K ≫ F ⟨2 * s + 1, by omega⟩ := by
  rw [zeroEqualityCycleComponent_second_attachment_conic_assoc hπ data D s hs hstart
    hk hp hpos, zeroEqualityPositiveCycleGlobalDesc_attachment_second,
    zeroEqualityPositiveCycleSecondAttachmentDesc_conic]

/-- The final first-chain chart keeps its full arbitrary-constant node branch. -/
@[reassoc] theorem zeroEqualityPositiveCycleGlobalDesc_terminal_first_chart :
    ProjectiveLine.left K ≫ (Z ⟨s, by omega⟩).left ≫ d =
      ProjectiveLine.left K ≫ F ⟨s, by omega⟩ := by
  rw [zeroEqualityCycleComponent_terminal_first_lineBranch_assoc hπ data D s hs hstart
    hk hp hpos, zeroEqualityPositiveCycleGlobalDesc_terminal_first,
    zeroEqualityCycleTerminalFirstDesc_line]

/-- The final second-chain chart keeps the opposite reciprocal tangent scale. -/
@[reassoc] theorem zeroEqualityPositiveCycleGlobalDesc_terminal_second_chart :
    ProjectiveLine.right K ≫ (Z ⟨s + 2, by omega⟩).left ≫ d =
      ProjectiveLine.right K ≫ F ⟨s + 2, by omega⟩ := by
  rw [zeroEqualityCycleComponent_terminal_second_lineBranch_assoc hπ data D s hs hstart
    hk hp hpos, zeroEqualityPositiveCycleGlobalDesc_terminal_second,
    zeroEqualityCycleTerminalSecondDesc_line]

end FLT.Mazur.WeierstrassDividedDepth
