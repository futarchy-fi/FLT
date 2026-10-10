/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalRetainedBranchCompatibility
public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroCyclePositiveTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroCycleLocalMaps
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasFamily

/-!
# The terminal and last positive tensor descents are compatible

The fixed terminal family and last positive family have the required four
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
  (D : SplitNodeDepth W π depth) (t : ℕ) (hs : t + 1 + 1 ≤ n)
  (hstart : start = 0) (hp : 2 * (start + (t + 1) + 1) < depth)
local notation "K" => ResidueField R
local notation "lastJ" => (Fin.last t)
local notation "g" => globalSuccessiveTensorChart hπ data K (t + 1) hs
local notation "T" => terminalNodeChart hπ data D (t + 1 + 1) hs (by omega) (by omega) hp
local notation "V" => terminalNodeAtlasIso hπ data D (t + 1 + 1) hs (by omega) (by omega) hp
variable {Y : Scheme.{u}}
  (F : Fin (2 * (t + 1) + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "dT" => Iso.hom V ≫
  zeroSplitCycleAtlasFamily hπ data D (t + 1) hs hstart hp F w (Fin.succ 0)
local notation "d" => zeroSplitCyclePositiveTensorDesc hπ data (t + 1) hs lastJ D hstart hp F w

/-- The fixed terminal and last positive descents agree on the entire tensor intersection. -/
theorem zeroSplitCycleTerminalPositiveTensorDesc_compatible :
    Limits.pullback.fst T g ≫ dT = Limits.pullback.snd T g ≫ d := by
  apply terminalPositiveRetained_compatible_of_branch_restrictions
    hπ data D (t + 1) hs (by omega) hp (by omega) dT d
    (F ⟨t + 1 + 1, by omega⟩) (F ⟨t + 1 + 2, by omega⟩)
  · rw [zeroSplitCycleAtlasFamily_terminal, ← Category.assoc]
    exact zeroSplitCycleTerminalDesc_first hπ data D (t + 1) hs (by omega) hp F w
  · rw [zeroSplitCycleAtlasFamily_terminal, ← Category.assoc]
    exact zeroSplitCycleTerminalDesc_second hπ data D (t + 1) hs (by omega) hp F w
  · have H := zeroSplitCyclePositiveTensorDesc_first hπ data (t + 1) hs lastJ D hstart hp F w
    simp only [Fin.val_last] at H
    rw [H]
    exact zeroSplitCycleFirstLocalDesc_conic data D (t + 1) hs hstart hp lastJ F w
  · have H := zeroSplitCyclePositiveTensorDesc_second hπ data (t + 1) hs lastJ D hstart hp F w
    simp only [Fin.val_last] at H
    rw [H]
    have C := zeroSplitCycleSecondLocalDesc_conic data D (t + 1) hs hstart hp lastJ F w
    have he : (⟨2 * (t + 1) + 2 - ((Fin.last t).val + 1), by omega⟩ :
        Fin (2 * (t + 1) + 3)) = ⟨t + 1 + 2, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [he] at C
    exact C

end FLT.Mazur.WeierstrassDividedDepth
