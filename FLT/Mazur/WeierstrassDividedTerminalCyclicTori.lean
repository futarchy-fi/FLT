/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroSplitCycle
public import FLT.Mazur.PolygonAtlasSmoothLocus

/-!
# Original terminal cyclic coordinates

The cyclic normalization reverses the first projective component. Its torus
is therefore the positive terminal branch without inversion. The second
component retains the reciprocal negative branch, including at scale one.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)
local notation "F" => ResidueField R
local notation "G" => terminalNodeChart hπ data D (s + 1) hs (by omega) hk hp

/-- The entire right affine chart of the first terminal component is the positive branch. -/
@[reassoc] theorem finalTerminalComponent_first_right :
    ProjectiveLine.right F ≫ finalTerminalComponent hπ data D s hs hk hp 0 =
      PolygonCyclicAtlas.secondBranch F ≫ G := by
  by_cases h : 0 < start + s
  · rw [finalTerminalComponent_positive hπ data D s hs hk hp h]
    exact terminalFirstComponent_right hπ data D s hs h hk hp
  · rw [finalTerminalComponent_zero_depth hπ data D s hs hk hp (by omega)]
    exact terminalZeroFirstComponent_right hπ data D s hs (by omega) hk hp

/-- The entire right affine chart of the second terminal component is the negative branch. -/
@[reassoc] theorem finalTerminalComponent_second_right :
    ProjectiveLine.right F ≫ finalTerminalComponent hπ data D s hs hk hp 1 =
      PolygonCyclicAtlas.firstBranch F ≫ G := by
  by_cases h : 0 < start + s
  · rw [finalTerminalComponent_positive hπ data D s hs hk hp h]
    exact terminalSecondComponent_right hπ data D s hs h hk hp
  · rw [finalTerminalComponent_zero_depth hπ data D s hs hk hp (by omega)]
    exact terminalZeroSecondComponent_right hπ data D s hs (by omega) hk hp

variable (hstart : start = 0)
local notation "Z" => zeroSplitCycleComponent hπ data D s hs hstart hk hp

/-- The original positive cyclic torus is exactly the original positive terminal puncture. -/
@[reassoc] theorem zeroSplitCycleComponent_terminalPositive_torus :
    (PolygonPinching.torusToComponent F).left ≫ (Z ⟨s + 1, by omega⟩).left =
      PolygonNodeBranches.right F ≫ G := by
  rw [zeroSplitCycleComponent_first hπ data D s hs hstart hk hp ⟨s, by omega⟩,
    finalBranchComponent_terminal]
  change (ProjectiveLine.overlapLeft F ≫ ProjectiveLine.left F) ≫
    ProjectiveLine.endpointReversal F ≫ finalTerminalComponent hπ data D s hs hk hp 0 = _
  rw [Category.assoc, ProjectiveLine.left_endpointReversal_assoc,
    finalTerminalComponent_first_right, ← Category.assoc,
    PolygonCyclicAtlas.overlap_secondBranch]

/-- The negative cyclic torus uses the reciprocal of the original terminal branch coordinate. -/
@[reassoc] theorem zeroSplitCycleComponent_terminalNegative_torus :
    (PolygonPinching.torusToComponent F).left ≫ (Z ⟨s + 2, by omega⟩).left =
      (ProjectiveLine.inversion F).hom ≫ PolygonNodeBranches.left F ≫ G := by
  have hi : (⟨s + 2, by omega⟩ : Fin (2 * s + 3)) =
      ⟨2 * s + 2 - (⟨s, by omega⟩ : Fin (s + 1)).val, by omega⟩ := Fin.ext (by dsimp; omega)
  rw [hi, zeroSplitCycleComponent_second, finalBranchComponent_terminal]
  change (ProjectiveLine.overlapLeft F ≫ ProjectiveLine.left F) ≫
    finalTerminalComponent hπ data D s hs hk hp 1 = _
  rw [ProjectiveLine.overlap_condition, ProjectiveLine.overlapRight,
    Category.assoc, Category.assoc, finalTerminalComponent_second_right,
    ← Category.assoc (ProjectiveLine.overlapLeft F), PolygonCyclicAtlas.overlap_firstBranch]

end FLT.Mazur.WeierstrassDividedDepth
