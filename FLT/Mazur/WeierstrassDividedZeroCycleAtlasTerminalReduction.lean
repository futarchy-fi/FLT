/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCycleZeroAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroCycleZeroAtlasCompatibility
public import FLT.Mazur.WeierstrassDividedZeroCycleAtlasEndReduction
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasEndReduction
import all FLT.Mazur.WeierstrassDividedZeroCyclePositiveAtlasCompatibility
public import FLT.Mazur.WeierstrassDividedZeroCycleAtlasAdjacentReduction
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasAdjacentReduction
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasFamily

/-!
# Only the terminal neighbor remains in the original cyclic atlas

The start-zero and positive neighbor is now proved on its whole intersection.
For s = 0 it coincides with the terminal neighbor, so the reduction is uniform.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
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
local notation "C" => ZeroSplitCycleAtlasCompatible hπ data D s hs hstart hp F w

/-- All original atlas overlaps follow from the single terminal-neighbor equation. -/
theorem zeroSplitCycleAtlasCompatible_of_terminal_neighbor
    (hterminal : C (Fin.succ 0) ⟨2, by omega⟩) : ∀ i k, C i k := by
  apply zeroSplitCycleAtlasCompatible_of_end_neighbors
    hπ data D s hs hstart hp F w hterminal
  by_cases hs0 : 0 < s
  · exact zeroSplitCycleAtlasCompatible_zero_neighbor hπ data D s hs hstart hp hs0 F w
  · have hz : s = 0 := by omega
    subst s
    exact hterminal

/-- The full atlas compatibility is now equivalent to just its terminal-neighbor equality. -/
theorem zeroSplitCycleAtlasCompatible_iff_terminal_neighbor :
    (∀ i k, C i k) ↔ C (Fin.succ 0) ⟨2, by omega⟩ := by
  constructor
  · intro H
    exact H _ _
  · exact zeroSplitCycleAtlasCompatible_of_terminal_neighbor hπ data D s hs hstart hp F w

end FLT.Mazur.WeierstrassDividedDepth
