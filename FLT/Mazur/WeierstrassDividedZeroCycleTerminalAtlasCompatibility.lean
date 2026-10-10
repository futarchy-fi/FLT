/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCycleTerminalPositiveTensorCompatibility
public import FLT.Mazur.WeierstrassDividedZeroCycleTerminalZeroTensorCompatibility
public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroCyclePositiveAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroCycleTerminalPositiveTensorCompatibility
import all FLT.Mazur.WeierstrassDividedZeroCycleTerminalZeroTensorCompatibility
import all FLT.Mazur.WeierstrassDividedZeroCyclePositiveTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroCycleZeroTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasFamily
public import FLT.Mazur.WeierstrassDividedTerminalParameterOrigins

/-!
# Full terminal-neighbor compatibility on the original fixed atlas

Both the positive last retained chart and the start-zero chart transport from
the proved whole tensor intersection. This includes the three-component cycle.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open Limits
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hstart : start = 0)
local notation "K" => ResidueField R

section Zero
variable (hs : 0 + 1 ≤ n) (hp : 2 * (start + 0 + 1) < depth)
local notation "m" => globalTensorAtlasMap hπ data K (0 + 1) hs
local notation "T" => terminalNodeChart hπ data D (0 + 1) hs (by omega) (by omega) hp
local notation "V" => terminalNodeAtlasIso hπ data D (0 + 1) hs (by omega) (by omega) hp
local notation "g" => globalSuccessiveTensorChart hπ data K 0 hs
variable {Y : Scheme.{u}} (F : Fin 3 → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "d" => zeroSplitCycleAtlasFamily hπ data D 0 hs hstart hp F w

/-- The three-component cycle has its full terminal and oldest atlas overlap equality. -/
theorem zeroSplitCycleAtlasCompatible_terminal_zero_neighbor :
    ZeroSplitCycleAtlasCompatible hπ data D 0 hs hstart hp F w (Fin.succ 0) ⟨2, by omega⟩ := by
  apply pullback_compatible_of_source_isos V (zeroSplitCycleZeroAtlasIso hπ data 0 hs)
    T g (m (Fin.succ 0)) (m ⟨2, by omega⟩) (d (Fin.succ 0)) (d ⟨2, by omega⟩) rfl
  · rw [terminalNodeAtlasIso_map]
  · rw [zeroSplitCycleZeroAtlasIso_global]
    apply (comp_eqToHom_heq _ _).trans
    exact heq_of_eq (olderGlobalTensorChart_zero_retention hπ data 0 hs)
  · have H := zeroSplitCycleTerminalZeroTensorDesc_compatible hπ data D hs hstart hp F w
    simpa only [zeroSplitCycleZeroTensorDesc, Category.assoc] using H

end Zero

section Positive
variable (t : ℕ) (hs : t + 1 + 1 ≤ n) (hp : 2 * (start + (t + 1) + 1) < depth)
local notation "j" => Fin.last t
local notation "i" => (Fin.mk (t + 1 - Fin.val j + 1) (by omega) : Fin (t + 1 + 1 + 3))
local notation "m" => globalTensorAtlasMap hπ data K (t + 1 + 1) hs
local notation "T" => terminalNodeChart hπ data D (t + 1 + 1) hs (by omega) (by omega) hp
local notation "V" => terminalNodeAtlasIso hπ data D (t + 1 + 1) hs (by omega) (by omega) hp
local notation "g" => globalSuccessiveTensorChart hπ data K (t + 1) hs
variable {Y : Scheme.{u}}
  (F : Fin (2 * (t + 1) + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ index, ProjectiveLine.zero (ResidueField R) ≫ F index =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) index))
local notation "d" => zeroSplitCycleAtlasFamily hπ data D (t + 1) hs hstart hp F w

/-- A positive last retained chart has its full terminal overlap at the original atlas indices. -/
theorem zeroSplitCycleAtlasCompatible_terminal_positive_neighbor :
    ZeroSplitCycleAtlasCompatible hπ data D (t + 1) hs hstart hp F w
      (Fin.succ 0) ⟨2, by omega⟩ := by
  have hi : i = ⟨2, by omega⟩ := Fin.ext (by dsimp; omega)
  rw [← hi]
  apply pullback_compatible_of_source_isos V
    (zeroSplitCyclePositiveAtlasIso hπ data (t + 1) hs j)
    T g (m (Fin.succ 0)) (m i) (d (Fin.succ 0)) (d i) rfl
  · rw [terminalNodeAtlasIso_map]
  · rw [zeroSplitCyclePositiveAtlasIso_global]
    apply (comp_eqToHom_heq _ _).trans
    exact (olderGlobalTensorChart_retention_heq hπ data (t + 1) hs
      (t + 1 - (t + 1)) 0 (by omega) hs (Nat.sub_self _)).trans
        (heq_of_eq (olderGlobalTensorChart_zero_retention hπ data (t + 1) hs))
  · have H := zeroSplitCycleTerminalPositiveTensorDesc_compatible
      hπ data D t hs hstart hp F w
    simpa only [zeroSplitCyclePositiveTensorDesc, Category.assoc] using H

end Positive

variable (s : ℕ) (hs : s + 1 ≤ n) (hp : 2 * (start + s + 1) < depth)
  {Y : Scheme.{u}} (F : Fin (2 * s + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))

/-- The terminal and its last retained neighbor agree on their whole actual intersection. -/
theorem zeroSplitCycleAtlasCompatible_terminal_neighbor :
    ZeroSplitCycleAtlasCompatible hπ data D s hs hstart hp F w (Fin.succ 0) ⟨2, by omega⟩ := by
  cases s with
  | zero =>
    exact zeroSplitCycleAtlasCompatible_terminal_zero_neighbor hπ data D hstart hs hp F w
  | succ t =>
    exact zeroSplitCycleAtlasCompatible_terminal_positive_neighbor hπ data D hstart t hs hp F w

end FLT.Mazur.WeierstrassDividedDepth
