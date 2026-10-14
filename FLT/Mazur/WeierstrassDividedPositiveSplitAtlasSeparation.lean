/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCycleAtlasTerminalNonadjacent
public import FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasSeparation
public import FLT.Mazur.WeierstrassDividedPositiveSplitAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedPositiveSplitAtlasCompatibility

/-!
# Empty terminal overlaps in the original strict-depth atlas

The entire terminal atlas chart lies in its two complete original components.
Its positive-scale exclusions give empty scheme intersections with infinity
and with every retained chart beyond its immediate neighbor.
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
local notation "m" => globalTensorAtlasMap hπ data K (s + 1) hs
variable (hstart : 0 < start) {Y : Scheme.{u}}
  (F : Fin (2 * s + 5) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "C" => PositiveSplitAtlasCompatible hπ data D s hs hstart hk hp F w

/-- Terminal versus infinity compatibility holds on the actual empty scheme intersection. -/
theorem positiveSplitAtlasCompatible_terminal_infinity : C (Fin.succ 0) 0 := by
  let _ := Scheme.isEmpty_pullback _ _
    (zeroSplitCycleAtlas_terminal_infinity_disjoint hπ data D s hs hk hp)
  exact isInitialOfIsEmpty.hom_ext _ _

/-- Every nonadjacent terminal overlap satisfies the full scheme compatibility equation. -/
theorem positiveSplitAtlasCompatible_terminal_nonadjacent
    (k : Fin (s + 1 + 3)) (hk3 : 3 ≤ k.val) : C (Fin.succ 0) k := by
  let i : Fin (s + 1) := ⟨k.val - 3, by omega⟩
  have H := precedingGlobalTensorAtlas_range_subset hπ data s hs 0 hs K i
  have hi : (Fin.succ ⟨i.val + 1 + 0 + 1, by omega⟩ : Fin (s + 1 + 0 + 3)) =
      k := Fin.ext (by dsimp [i]; omega)
  rw [hi] at H
  let _ := Scheme.isEmpty_pullback _ _
    ((terminalAtlas_precedingExterior_disjoint hπ data D s hs hk hp (by omega)).mono_right H)
  exact isInitialOfIsEmpty.hom_ext _ _

/-- The full first retained/infinity overlap is empty as well, with no positive s assumption. -/
theorem positiveSplitAtlasCompatible_retained_infinity
    (i : Fin (s + 1 + 3)) (hi : 2 ≤ i.val) (hil : i.val ≤ s + 2) : C i 0 := by
  let _ := Scheme.isEmpty_pullback _ _
    (positiveEqualityAtlas_retained_infinity_disjoint hπ data D s hs hstart i hi hil)
  exact isInitialOfIsEmpty.hom_ext _ _

end FLT.Mazur.WeierstrassDividedDepth
