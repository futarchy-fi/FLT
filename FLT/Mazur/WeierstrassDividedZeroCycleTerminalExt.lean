/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalAtlasPushout
public import FLT.Mazur.WeierstrassDividedZeroSplitCycle

/-!
# Terminal atlas branches in the actual cyclic component family

Endpoint reversal changes the first terminal component's right chart to the
left chart. Both branches detect morphisms on the exact original atlas object.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "G" => globalTensorAtlasMap hπ data K (s + 1) hs (Fin.succ 0)
local notation "Z" => zeroSplitCycleComponent hπ data D s hs hstart hk hp

/-- The first ordered terminal branch is the left chart after cyclic reversal. -/
@[reassoc] theorem zeroSplitCycleComponent_terminal_first_branch :
    terminalAtlasFirstBranch hπ data D s hs hk hp ≫ G =
      ProjectiveLine.left K ≫ (Z ⟨s + 1, by omega⟩).left := by
  rw [terminalAtlasFirstBranch_global]
  have H := congrArg Over.Hom.left
    (zeroSplitCycleComponent_first hπ data D s hs hstart hk hp ⟨s, by omega⟩)
  rw [H]
  change _ = ProjectiveLine.left K ≫ ProjectiveLine.endpointReversal K ≫
    (finalBranchComponent hπ data D s hs hk hp ⟨s, by omega⟩ 0).left
  rw [ProjectiveLine.left_endpointReversal_assoc, finalBranchComponent_terminal]
  rfl

/-- The opposite terminal branch keeps the right chart and cyclic successor index. -/
@[reassoc] theorem zeroSplitCycleComponent_terminal_second_branch :
    terminalAtlasSecondBranch hπ data D s hs hk hp ≫ G =
      ProjectiveLine.right K ≫ (Z ⟨s + 2, by omega⟩).left := by
  rw [terminalAtlasSecondBranch_global]
  have hi : (⟨s + 2, by omega⟩ : Fin (2 * s + 3)) =
      ⟨2 * s + 2 - (⟨s, by omega⟩ : Fin (s + 1)).val, by omega⟩ :=
    Fin.ext (by dsimp; omega)
  rw [hi, zeroSplitCycleComponent_second, finalBranchComponent_terminal]
  rfl

variable {Y : Scheme.{u}}
  (f g : finiteGlobalTensorModel hπ data (ResidueField R) (s + 1) hs ⟶ Y)
  (h : ∀ i, (zeroSplitCycleComponent hπ data D s hs hstart hk hp i).left ≫ f =
    (zeroSplitCycleComponent hπ data D s hs hstart hk hp i).left ≫ g)

include h in
/-- Component agreement determines the entire original terminal chart for any target. -/
theorem zeroSplitCycleComponent_terminal_hom_ext : G ≫ f = G ≫ g := by
  apply (terminalAtlasBranches_isPushout hπ data D s hs hk hp).hom_ext
  · simpa only [zeroSplitCycleComponent_terminal_first_branch_assoc
      hπ data D s hs hstart hk hp] using
      congrArg (fun q => ProjectiveLine.left K ≫ q) (h ⟨s + 1, by omega⟩)
  · simpa only [zeroSplitCycleComponent_terminal_second_branch_assoc
      hπ data D s hs hstart hk hp] using
      congrArg (fun q => ProjectiveLine.right K ≫ q) (h ⟨s + 2, by omega⟩)

end FLT.Mazur.WeierstrassDividedDepth
