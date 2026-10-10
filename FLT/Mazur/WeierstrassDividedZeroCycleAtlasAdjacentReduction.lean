/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCycleAtlasInfinityCompatibility
public import FLT.Mazur.WeierstrassDividedZeroCycleAtlasTerminalNonadjacent
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasInfinityCompatibility
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasTerminalNonadjacent

/-!
# Only adjacent retained-chart compatibility remains on the cyclic atlas

All infinity and initial-chart equations are proved. Together with the empty
nonadjacent intersections they reduce full atlas compatibility to adjacent pairs.
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

/-- Every original atlas chart is compatible with the entire infinity chart. -/
theorem zeroSplitCycleAtlasCompatible_infinity (i : Fin (s + 1 + 3)) : C i 0 := by
  by_cases h0 : i = 0
  · subst i
    exact zeroSplitCycleAtlasCompatible_self hπ data D s hs hstart hp F w 0
  by_cases h1 : i = Fin.succ 0
  · subst i
    exact zeroSplitCycleAtlasCompatible_terminal_infinity hπ data D s hs hstart hp F w
  by_cases h2 : i = ⟨s + 2, by omega⟩
  · subst i
    exact zeroSplitCycleAtlasCompatible_zero_infinity hπ data D s hs hstart hp F w
  by_cases h3 : i = ⟨s + 3, by omega⟩
  · subst i
    exact zeroSplitCycleAtlasCompatible_initial_infinity hπ data D s hs hstart hp F w
  have hi0 : i.val ≠ 0 := fun h => h0 (Fin.ext h)
  have hi1 : i.val ≠ 1 := fun h => h1 (Fin.ext h)
  have hi2 : i.val ≠ s + 2 := fun h => h2 (Fin.ext h)
  have hi3 : i.val ≠ s + 3 := fun h => h3 (Fin.ext h)
  exact zeroSplitCycleAtlasCompatible_positive_infinity hπ data D s hs hstart hp F w i
    (by omega) (by omega)

/-- Every original chart is compatible with the redundant initial chart. -/
theorem zeroSplitCycleAtlasCompatible_initial (i : Fin (s + 1 + 3)) :
    C i ⟨s + 3, by omega⟩ :=
  zeroSplitCycleAtlasCompatible_initial_of_infinity hπ data D s hs hstart hp F w i
    (zeroSplitCycleAtlasCompatible_infinity hπ data D s hs hstart hp F w i)

/-- Full original-atlas compatibility follows once the adjacent noninitial equations are proved. -/
theorem zeroSplitCycleAtlasCompatible_of_adjacent
    (H : ∀ i j : Fin (s + 1 + 3), 1 ≤ i.val → j.val = i.val + 1 →
      j.val ≤ s + 2 → C i j) : ∀ i j, C i j := by
  have ordered : ∀ i j : Fin (s + 1 + 3), i.val ≤ j.val → C i j := by
    intro i j hij
    by_cases hi0 : i = 0
    · subst i
      exact zeroSplitCycleAtlasCompatible_symm hπ data D s hs hstart hp F w
        (zeroSplitCycleAtlasCompatible_infinity hπ data D s hs hstart hp F w j)
    by_cases hjlast : j = ⟨s + 3, by omega⟩
    · rw [hjlast]
      exact zeroSplitCycleAtlasCompatible_initial hπ data D s hs hstart hp F w i
    by_cases he : i = j
    · subst j
      exact zeroSplitCycleAtlasCompatible_self hπ data D s hs hstart hp F w i
    have hi : 1 ≤ i.val := by
      have h : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
      omega
    have hj : j.val ≤ s + 2 := by
      have h : j.val ≠ s + 3 := fun h => hjlast (Fin.ext h)
      omega
    by_cases hadj : j.val = i.val + 1
    · exact H i j hi hadj hj
    have hgap : i.val + 2 ≤ j.val := by
      have h : i.val ≠ j.val := fun h => he (Fin.ext h)
      omega
    by_cases hi1 : i = Fin.succ 0
    · subst i
      exact zeroSplitCycleAtlasCompatible_terminal_nonadjacent
        hπ data D s hs hp hstart F w j (by simpa using hgap)
    have hi2 : 2 ≤ i.val := by
      have h : i.val ≠ 1 := fun h => hi1 (Fin.ext h)
      omega
    exact zeroSplitCycleAtlasCompatible_symm hπ data D s hs hstart hp F w
      (zeroSplitCycleAtlasCompatible_nonadjacent hπ data D s hs hstart hp F w i j hi2 hgap)
  intro i j
  rcases le_total i.val j.val with hij | hji
  · exact ordered i j hij
  · exact zeroSplitCycleAtlasCompatible_symm hπ data D s hs hstart hp F w (ordered j i hji)

/-- The remaining adjacent equations are exactly the outstanding condition for global descent. -/
theorem zeroSplitCycleAtlasCompatible_iff_adjacent :
    (∀ i j, C i j) ↔ ∀ i j : Fin (s + 1 + 3),
      1 ≤ i.val → j.val = i.val + 1 → j.val ≤ s + 2 → C i j := by
  constructor
  · intro H i j _ _ _
    exact H i j
  · exact zeroSplitCycleAtlasCompatible_of_adjacent hπ data D s hs hstart hp F w

end FLT.Mazur.WeierstrassDividedDepth
