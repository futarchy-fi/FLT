/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitGlobalDesc
import all FLT.Mazur.WeierstrassDividedPositiveSplitGlobalDesc
import all FLT.Mazur.WeierstrassDividedPositiveSplitAtlasFamily
import all FLT.Mazur.WeierstrassDividedPositiveSplitTerminalMap

/-!
# Both original terminal branches recover their cyclic projective charts

Strict depth gives two distinct terminal components. Their full affine
charts are recovered from the actual two-branch terminal pushout.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 5) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "K" => ResidueField R
local notation "d" => positiveSplitCycleGlobalDesc hπ data D s hs hstart hk hp F w
local notation "Z" => positiveSplitCycleComponent hπ data D s hs hstart hk hp
/-- The complete first terminal branch keeps its prescribed projective chart. -/
@[reassoc] theorem positiveSplitCycleGlobalDesc_terminal_first_chart :
    ProjectiveLine.left K ≫ (Z ⟨s + 2, by omega⟩).left ≫ d =
      ProjectiveLine.left K ≫ F ⟨s + 2, by omega⟩ := by
  rw [← positiveSplitCycleComponent_terminal_first_branch_assoc,
    positiveSplitCycleGlobalDesc_atlas, positiveSplitCycleAtlasFamily_terminal,
    positiveSplitCycleTerminalDesc_first]

/-- The complete second terminal branch keeps its prescribed projective chart. -/
@[reassoc] theorem positiveSplitCycleGlobalDesc_terminal_second_chart :
    ProjectiveLine.right K ≫ (Z ⟨s + 3, by omega⟩).left ≫ d =
      ProjectiveLine.right K ≫ F ⟨s + 3, by omega⟩ := by
  rw [← positiveSplitCycleComponent_terminal_second_branch_assoc,
    positiveSplitCycleGlobalDesc_atlas, positiveSplitCycleAtlasFamily_terminal,
    positiveSplitCycleTerminalDesc_second]

end FLT.Mazur.WeierstrassDividedDepth
