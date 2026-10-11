/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityAtlasTerminalSeparation
public import FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasCompatibility

/-!
# Empty terminal overlaps in the original equality-depth atlas

The entire Laurent atlas chart lies in the complete terminal component.
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
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "m" => globalTensorAtlasMap hπ data K (s + 1) hs
variable (hstart : 0 < start) {Y : Scheme.{u}}
  (F : Fin (2 * s + 4) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "C" => PositiveEqualityAtlasCompatible hπ data D s hs hstart hk hp F w

/-- Terminal versus infinity compatibility holds on the actual empty scheme intersection. -/
theorem positiveEqualityAtlasCompatible_terminal_infinity : C (Fin.succ 0) 0 := by
  let _ := Scheme.isEmpty_pullback _ _
    (zeroEqualityAtlas_terminal_infinity_disjoint hπ data D s hs hk hp (by omega))
  exact isInitialOfIsEmpty.hom_ext _ _

/-- Every nonadjacent terminal overlap satisfies the full scheme compatibility equation. -/
theorem positiveEqualityAtlasCompatible_terminal_nonadjacent
    (k : Fin (s + 1 + 3)) (hk3 : 3 ≤ k.val) : C (Fin.succ 0) k := by
  let _ := Scheme.isEmpty_pullback _ _
    (zeroEqualityAtlas_terminal_nonadjacent_disjoint hπ data D s hs hk hp (by omega) k hk3)
  exact isInitialOfIsEmpty.hom_ext _ _

include hstart D in
/-- Every retained chart, including the first pair at positive start, misses infinity. -/
theorem positiveEqualityAtlas_retained_infinity_disjoint
    (i : Fin (s + 1 + 3)) (hi : 2 ≤ i.val) (hil : i.val ≤ s + 2) :
    Disjoint (Set.range (m i)) (Set.range (m 0)) := by
  let j := s + 2 - i.val
  let r := i.val - 2
  have he : j + 1 + r = s + 1 := by dsimp [j, r]; omega
  have H := olderSplitNode_infinity_disjoint hπ data j (by dsimp [j]; omega)
    r (by omega) (by dsimp [j]; omega) D
  exact (globalTensorAtlas_disjoint_index_congr hπ data K (by omega) hs he
    _ _ i 0 (by dsimp [r]; omega) rfl).mp H

/-- The full first retained/infinity overlap is empty as well, with no positive s assumption. -/
theorem positiveEqualityAtlasCompatible_retained_infinity
    (i : Fin (s + 1 + 3)) (hi : 2 ≤ i.val) (hil : i.val ≤ s + 2) : C i 0 := by
  let _ := Scheme.isEmpty_pullback _ _
    (positiveEqualityAtlas_retained_infinity_disjoint hπ data D s hs hstart i hi hil)
  exact isInitialOfIsEmpty.hom_ext _ _

end FLT.Mazur.WeierstrassDividedDepth
