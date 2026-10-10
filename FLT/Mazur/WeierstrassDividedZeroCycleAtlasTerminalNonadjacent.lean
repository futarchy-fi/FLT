/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPrecedingAtlasRange
public import FLT.Mazur.WeierstrassDividedOlderConicExteriorDisjoint
public import FLT.Mazur.WeierstrassDividedZeroCycleAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasCompatibility

/-!
# The terminal chart misses every nonadjacent original atlas chart

The complete terminal components miss the full preceding exterior by density
and the conic exclusion. The initial chart is also handled when the chain is empty.
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
local notation "K" => ResidueField R
local notation "X" => olderGlobalExteriorTensorChart hπ data K s hs 0 hs
local notation "G" => globalTensorAtlasMap hπ data K (s + 1) hs (Fin.succ 0)

/-- At positive depth the entire left terminal parameter lies in the original retained conic. -/
theorem finalTerminalComponent_positive_left_range_conic (hpos : 0 < start + s) (i : Fin 2) :
    Set.range (ProjectiveLine.left K ≫ finalTerminalComponent hπ data D s hs hk hp i) ⊆
      Set.range (olderGlobalMiddleConic hπ data D s hs 0 hs hpos hk) := by
  rw [finalTerminalComponent_positive hπ data D s hs hk hp hpos]
  fin_cases i
  · change Set.range (ProjectiveLine.left K ≫
      terminalFirstComponent hπ data D s hs hpos hk hp) ⊆ _
    rw [terminalFirstComponent_left, terminalConicFirstParameter_retained]
    rintro _ ⟨a, rfl⟩
    exact ⟨_, rfl⟩
  · change Set.range (ProjectiveLine.left K ≫
      terminalSecondComponent hπ data D s hs hpos hk hp) ⊆ _
    rw [terminalSecondComponent_left, terminalConicSecondParameter_retained]
    rintro _ ⟨a, rfl⟩
    exact ⟨_, rfl⟩

/-- The complete terminal components miss the full original preceding exterior. -/
theorem finalTerminalComponent_precedingExterior_disjoint
    (hpos : 0 < start + s) (i : Fin 2) :
    Disjoint (Set.range (finalTerminalComponent hπ data D s hs hk hp i))
      (Set.range X) := by
  apply ProjectiveLine.map_range_open_disjoint_of_left K
  exact (olderGlobalConicExterior_disjoint hπ data D s hs 0 hs hpos hk).symm.mono_left
    (finalTerminalComponent_positive_left_range_conic hπ data D s hs hk hp hpos i)

include D hk hp in
/-- No point of the entire terminal chart lies in any part of the preceding exterior. -/
theorem terminalAtlas_precedingExterior_disjoint (hpos : 0 < start + s) :
    Disjoint (Set.range G) (Set.range X) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨z, rfl⟩ hz
  rcases terminalAtlasBranches_cover hπ data D s hs hk hp z with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · have he := congrArg (fun f => f a)
      (terminalAtlasFirstBranch_global hπ data D s hs hk hp)
    exact Set.disjoint_left.mp
      (finalTerminalComponent_precedingExterior_disjoint hπ data D s hs hk hp hpos 0)
      ⟨ProjectiveLine.right K a, he.symm⟩ hz
  · have he := congrArg (fun f => f a)
      (terminalAtlasSecondBranch_global hπ data D s hs hk hp)
    exact Set.disjoint_left.mp
      (finalTerminalComponent_precedingExterior_disjoint hπ data D s hs hk hp hpos 1)
      ⟨ProjectiveLine.right K a, he.symm⟩ hz

variable (hstart : start = 0)
local notation "m" => globalTensorAtlasMap hπ data K (s + 1) hs

include D hk hp hstart in
/-- At fixed atlas indices every chart beyond the neighbor is disjoint from the terminal chart. -/
theorem zeroSplitCycleAtlas_terminal_nonadjacent_disjoint
    (k : Fin (s + 1 + 3)) (hk3 : 3 ≤ k.val) :
    Disjoint (Set.range (m (Fin.succ 0))) (Set.range (m k)) := by
  by_cases hpos : 0 < start + s
  · let i : Fin (s + 1) := ⟨k.val - 3, by omega⟩
    have H := precedingGlobalTensorAtlas_range_subset hπ data s hs 0 hs K i
    have hi : (Fin.succ ⟨i.val + 1 + 0 + 1, by omega⟩ : Fin (s + 1 + 0 + 3)) =
        k := Fin.ext (by dsimp [i]; omega)
    rw [hi] at H
    exact (terminalAtlas_precedingExterior_disjoint hπ data D s hs hk hp hpos).mono_right H
  · have he : k = ⟨s + 3, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [he]
    apply (zeroSplitCycleAtlas_terminal_infinity_disjoint hπ data D s hs hk hp).mono_right
    rintro _ ⟨a, rfl⟩
    refine ⟨zeroSplitCycleInitialToInfinity hπ data D s hs hstart hk a, ?_⟩
    exact congrArg (fun f => f a)
      (zeroSplitCycleInitialToInfinity_global hπ data D s hs hstart hk)

variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))

/-- Every terminal/nonadjacent atlas overlap satisfies the actual scheme compatibility equation. -/
theorem zeroSplitCycleAtlasCompatible_terminal_nonadjacent
    (k : Fin (s + 1 + 3)) (hk3 : 3 ≤ k.val) :
    ZeroSplitCycleAtlasCompatible hπ data D s hs hstart hp F w (Fin.succ 0) k := by
  let _ : IsEmpty (Limits.pullback (m (Fin.succ 0)) (m k) : Scheme) :=
    Scheme.isEmpty_pullback _ _
      (zeroSplitCycleAtlas_terminal_nonadjacent_disjoint hπ data D s hs (by omega) hp hstart k hk3)
  exact isInitialOfIsEmpty.hom_ext _ _

end FLT.Mazur.WeierstrassDividedDepth
