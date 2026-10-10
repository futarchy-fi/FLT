/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCycleGlobalDesc
public import FLT.Mazur.WeierstrassDividedZeroCycleZeroAtlasConics
import all FLT.Mazur.WeierstrassDividedZeroCycleGlobalDesc
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasFamily

/-!
# Global descent at the end charts of the cyclic chains

Both oldest conic charts and both terminal branches recover their prescribed
family maps, including the zero-length chain case.
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
  (hstart : start = 0) (hp : 2 * (start + s + 1) < depth)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "K" => ResidueField R
local notation "d" => zeroSplitCycleGlobalDesc hπ data D s hs hstart hp F w

local notation "Z" => zeroSplitCycleComponent hπ data D s hs hstart (by omega) hp

/-- The first oldest conic chart retains the prescribed cyclic map. -/
@[reassoc] theorem zeroSplitCycleGlobalDesc_attachment_first_chart :
    ProjectiveLine.right K ≫ (Z 1).left ≫ d =
      ProjectiveLine.right K ≫ F 1 := by
  rw [← zeroSplitCycleZeroAtlasFirstConic_global_assoc hπ data D s hs hstart hp,
    zeroSplitCycleGlobalDesc_atlas, zeroSplitCycleZeroAtlasFirstConic_desc]

/-- The second oldest conic chart retains the prescribed cyclic map. -/
@[reassoc] theorem zeroSplitCycleGlobalDesc_attachment_second_chart :
    ProjectiveLine.left K ≫ (Z ⟨2 * s + 2, by omega⟩).left ≫ d =
      ProjectiveLine.left K ≫ F ⟨2 * s + 2, by omega⟩ := by
  rw [← zeroSplitCycleZeroAtlasSecondConic_global_assoc hπ data D s hs hstart hp,
    zeroSplitCycleGlobalDesc_atlas, zeroSplitCycleZeroAtlasSecondConic_desc]

/-- The first terminal branch keeps its original cyclic orientation. -/
@[reassoc] theorem zeroSplitCycleGlobalDesc_terminal_first_chart :
    ProjectiveLine.left K ≫ (Z ⟨s + 1, by omega⟩).left ≫ d =
      ProjectiveLine.left K ≫ F ⟨s + 1, by omega⟩ := by
  rw [← zeroSplitCycleComponent_terminal_first_branch_assoc
    hπ data D s hs hstart (by omega) hp,
    zeroSplitCycleGlobalDesc_atlas, zeroSplitCycleAtlasFamily_terminal,
    zeroSplitCycleTerminalDesc_first]

/-- The second terminal branch keeps its original cyclic orientation. -/
@[reassoc] theorem zeroSplitCycleGlobalDesc_terminal_second_chart :
    ProjectiveLine.right K ≫ (Z ⟨s + 2, by omega⟩).left ≫ d =
      ProjectiveLine.right K ≫ F ⟨s + 2, by omega⟩ := by
  rw [← zeroSplitCycleComponent_terminal_second_branch_assoc
    hπ data D s hs hstart (by omega) hp,
    zeroSplitCycleGlobalDesc_atlas, zeroSplitCycleAtlasFamily_terminal,
    zeroSplitCycleTerminalDesc_second]

end FLT.Mazur.WeierstrassDividedDepth
