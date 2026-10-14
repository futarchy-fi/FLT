/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalRetainedBranchCompatibility
public import FLT.Mazur.WeierstrassDividedPositiveSplitRetainedTensorDesc
import all FLT.Mazur.WeierstrassDividedPositiveSplitRetainedTensorDesc
import all FLT.Mazur.WeierstrassDividedPositiveSplitLocalMaps
import all FLT.Mazur.WeierstrassDividedPositiveSplitAtlasFamily

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
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "lastJ" => (Fin.last s)
local notation "g" => globalSuccessiveTensorChart hπ data K s hs
local notation "T" => terminalNodeChart hπ data D (s + 1) hs (by omega) (by omega) hp
local notation "V" => terminalNodeAtlasIso hπ data D (s + 1) hs (by omega) (by omega) hp
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 5) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "dT" => Iso.hom V ≫
  positiveSplitCycleAtlasFamily hπ data D s hs hstart hk hp F w (Fin.succ 0)
local notation "d" => positiveSplitCycleRetainedTensorDesc hπ data D s hs hstart hk hp lastJ F w

/-- The fixed terminal and last positive descents agree on the entire tensor intersection. -/
theorem positiveSplitCycleTerminalPositiveTensorDesc_compatible :
    Limits.pullback.fst T g ≫ dT = Limits.pullback.snd T g ≫ d := by
  apply terminalPositiveRetained_compatible_of_branch_restrictions
    hπ data D s hs (by omega) hp (by omega) dT d
    (F ⟨s + 2, by omega⟩) (F ⟨s + 3, by omega⟩)
  · rw [positiveSplitCycleAtlasFamily_terminal, ← Category.assoc]
    exact positiveSplitCycleTerminalDesc_first hπ data D s hs (by omega) hp F w
  · rw [positiveSplitCycleAtlasFamily_terminal, ← Category.assoc]
    exact positiveSplitCycleTerminalDesc_second hπ data D s hs (by omega) hp F w
  · have H := positiveSplitCycleRetainedTensorDesc_first hπ data D s hs hstart hk hp lastJ F w
    simp only [Fin.val_last] at H
    rw [H]
    exact positiveSplitCycleFirstLocalDesc_conic data D s hs hp lastJ F w
  · have H := positiveSplitCycleRetainedTensorDesc_second hπ data D s hs hstart hk hp lastJ F w
    simp only [Fin.val_last] at H
    rw [H]
    have C := positiveSplitCycleSecondLocalDesc_conic data D s hs hp lastJ F w
    have he : (⟨2 * s + 4 - ((Fin.last s).val + 1), by omega⟩ :
        Fin (2 * s + 5)) = ⟨s + 3, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [he] at C
    exact C

end FLT.Mazur.WeierstrassDividedDepth
