/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalRetainedBranchCompatibility
public import FLT.Mazur.WeierstrassDividedZeroCycleZeroTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroCycleZeroTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroCycleAttachmentMaps
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasFamily

/-!
# The terminal and start-zero tensor descents are compatible

The fixed terminal family and oldest family have the required four
branch restrictions, so they agree on their complete original intersection.
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
  (D : SplitNodeDepth W π depth) (hs : 0 + 1 ≤ n)
  (hstart : start = 0) (hp : 2 * (start + 0 + 1) < depth)
local notation "K" => ResidueField R
local notation "g" => globalSuccessiveTensorChart hπ data K 0 hs
local notation "T" => terminalNodeChart hπ data D (0 + 1) hs (by omega) (by omega) hp
local notation "V" => terminalNodeAtlasIso hπ data D (0 + 1) hs (by omega) (by omega) hp
variable {Y : Scheme.{u}}
  (F : Fin (3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "dT" => Iso.hom V ≫
  zeroSplitCycleAtlasFamily hπ data D 0 hs hstart hp F w (Fin.succ 0)
local notation "d" => zeroSplitCycleZeroTensorDesc hπ data 0 hs D hstart hp F w

/-- The fixed terminal and start-zero descents agree on the entire tensor intersection. -/
theorem zeroSplitCycleTerminalZeroTensorDesc_compatible :
    Limits.pullback.fst T g ≫ dT = Limits.pullback.snd T g ≫ d := by
  apply terminalZeroRetained_compatible_of_branch_restrictions
    hπ data D 0 hs (by omega) hp (by omega) dT d (F 1) (F 2)
  · rw [zeroSplitCycleAtlasFamily_terminal, ← Category.assoc]
    exact zeroSplitCycleTerminalDesc_first hπ data D 0 hs (by omega) hp F w
  · rw [zeroSplitCycleAtlasFamily_terminal, ← Category.assoc]
    exact zeroSplitCycleTerminalDesc_second hπ data D 0 hs (by omega) hp F w
  · simp only [Category.assoc]
    rw [zeroSplitCycleZeroTensorDesc_first]
    exact zeroSplitCycleFirstAttachmentDesc_conic data D 0 hs hp F w
  · simp only [Category.assoc]
    rw [zeroSplitCycleZeroTensorDesc_second]
    exact zeroSplitCycleSecondAttachmentDesc_conic data D 0 hs hp F w

end FLT.Mazur.WeierstrassDividedDepth
