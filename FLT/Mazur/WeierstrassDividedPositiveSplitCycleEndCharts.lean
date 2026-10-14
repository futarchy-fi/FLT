/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitCycle
public import FLT.Mazur.WeierstrassDividedTerminalAtlasPushout

/-!
# Original exterior and terminal atlas restrictions at strict depth

The full infinity chart and both terminal branches retain their cyclic component maps.
These scheme-map equations retain the original coordinates for subsequent descent.
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
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "ι" => initialExteriorInfinityChart hπ data D (s + 1) hs hstart (by omega)
local notation "E" => initialExteriorOrientedIso hπ data D (s + 1) hs hstart
  (by omega) (by omega)
local notation "Z" => positiveSplitCycleComponent hπ data D s hs hstart hk hp

/-- The complete original infinity tensor chart factors through cyclic component zero. -/
@[reassoc] theorem positiveSplitCycleComponent_infinity_chart :
    ι ≫ (E).hom ≫ (Z 0).left = finiteInfinityTensorChart hπ data K (s + 1) hs := by
  rw [positiveSplitCycleComponent_exterior,
    equalityInitialExteriorOverComponent_original,
    initialExteriorToGlobal_infinity]

/-- The first terminal branch is the left chart of its reversed cyclic component. -/
@[reassoc] theorem positiveSplitCycleComponent_terminal_first_branch :
    terminalAtlasFirstBranch hπ data D s hs hk hp ≫
        globalTensorAtlasMap hπ data K (s + 1) hs (Fin.succ 0) =
      ProjectiveLine.left K ≫ (Z ⟨s + 2, by omega⟩).left := by
  rw [terminalAtlasFirstBranch_global]
  have H := congrArg Over.Hom.left
    (positiveSplitCycleComponent_first hπ data D s hs hstart hk hp ⟨s + 1, by omega⟩)
  rw [H]
  change _ = ProjectiveLine.left K ≫ ProjectiveLine.endpointReversal K ≫
    (positiveSplitBranchComponent hπ data D s hs hstart hk hp ⟨s + 1, by omega⟩ 0).left
  rw [ProjectiveLine.left_endpointReversal_assoc,
    positiveSplitBranchComponent_tail hπ data D s hs hstart hk hp ⟨s, by omega⟩,
    finalBranchComponent_terminal]
  rfl

/-- The opposite complete terminal branch retains its right chart in the cyclic successor. -/
@[reassoc] theorem positiveSplitCycleComponent_terminal_second_branch :
    terminalAtlasSecondBranch hπ data D s hs hk hp ≫
        globalTensorAtlasMap hπ data K (s + 1) hs (Fin.succ 0) =
      ProjectiveLine.right K ≫ (Z ⟨s + 3, by omega⟩).left := by
  rw [terminalAtlasSecondBranch_global]
  have hi : (⟨s + 3, by omega⟩ : Fin (2 * s + 5)) =
      ⟨2 * s + 4 - (⟨s + 1, by omega⟩ : Fin (s + 2)).val, by omega⟩ :=
    Fin.ext (by dsimp; omega)
  rw [hi, positiveSplitCycleComponent_second,
    positiveSplitBranchComponent_tail hπ data D s hs hstart hk hp ⟨s, by omega⟩,
    finalBranchComponent_terminal]
  rfl

variable {Y : Scheme.{u}}
  (f g : finiteGlobalTensorModel hπ data (ResidueField R) (s + 1) hs ⟶ Y)
  (h : ∀ i, (positiveSplitCycleComponent hπ data D s hs hstart hk hp i).left ≫ f =
    (positiveSplitCycleComponent hπ data D s hs hstart hk hp i).left ≫ g)

include h in
/-- Cyclic component agreement determines the original infinity chart into any scheme. -/
theorem positiveSplitCycleComponent_infinity_hom_ext :
    globalTensorAtlasMap hπ data K (s + 1) hs 0 ≫ f =
      globalTensorAtlasMap hπ data K (s + 1) hs 0 ≫ g := by
  change finiteInfinityTensorChart hπ data K (s + 1) hs ≫ f =
    finiteInfinityTensorChart hπ data K (s + 1) hs ≫ g
  have H := congrArg (fun q => ι ≫ (E).hom ≫ q) (h 0)
  simpa only [positiveSplitCycleComponent_infinity_chart_assoc] using H

include h in
/-- Both terminal branches determine maps from the entire original terminal atlas object. -/
theorem positiveSplitCycleComponent_terminal_hom_ext :
    globalTensorAtlasMap hπ data K (s + 1) hs (Fin.succ 0) ≫ f =
      globalTensorAtlasMap hπ data K (s + 1) hs (Fin.succ 0) ≫ g := by
  apply (terminalAtlasBranches_isPushout hπ data D s hs hk hp).hom_ext
  · simpa only [positiveSplitCycleComponent_terminal_first_branch_assoc
      hπ data D s hs hstart hk hp] using
      congrArg (fun q => ProjectiveLine.left K ≫ q) (h ⟨s + 2, by omega⟩)
  · simpa only [positiveSplitCycleComponent_terminal_second_branch_assoc
      hπ data D s hs hstart hk hp] using
      congrArg (fun q => ProjectiveLine.right K ≫ q) (h ⟨s + 3, by omega⟩)

end FLT.Mazur.WeierstrassDividedDepth
