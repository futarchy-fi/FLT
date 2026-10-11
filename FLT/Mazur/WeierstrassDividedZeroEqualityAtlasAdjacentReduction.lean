/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityAtlasInfinityCompatibility
public import FLT.Mazur.WeierstrassDividedZeroEqualityAtlasTerminalSeparation
import all FLT.Mazur.WeierstrassDividedZeroEqualityAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroEqualityAtlasInfinityCompatibility
import all FLT.Mazur.WeierstrassDividedZeroEqualityAtlasTerminalSeparation

/-!
# Equality-depth global compatibility reduces to adjacent original charts

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
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth) (hpos : 0 < s)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 2) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "C" => ZeroEqualityPositiveAtlasCompatible hπ data D s hs hstart hk hp hpos F w

/-- Every original atlas chart is compatible with the entire infinity chart. -/
theorem zeroEqualityPositiveAtlasCompatible_infinity (i : Fin (s + 1 + 3)) : C i 0 := by
  by_cases h0 : i = 0
  · subst i
    exact zeroEqualityPositiveAtlasCompatible_self hπ data D s hs hstart hk hp hpos F w 0
  by_cases h1 : i = Fin.succ 0
  · subst i
    exact zeroEqualityPositiveAtlasCompatible_terminal_infinity hπ data D s hs hk hp hstart hpos F w
  by_cases h2 : i = ⟨s + 2, by omega⟩
  · subst i
    exact zeroEqualityPositiveAtlasCompatible_zero_infinity hπ data D s hs hstart hk hp hpos F w
  by_cases h3 : i = ⟨s + 3, by omega⟩
  · subst i
    exact zeroEqualityPositiveAtlasCompatible_initial_infinity hπ data D s hs hstart hk hp hpos F w
  have hi0 : i.val ≠ 0 := fun h => h0 (Fin.ext h)
  have hi1 : i.val ≠ 1 := fun h => h1 (Fin.ext h)
  have hi2 : i.val ≠ s + 2 := fun h => h2 (Fin.ext h)
  have hi3 : i.val ≠ s + 3 := fun h => h3 (Fin.ext h)
  exact zeroEqualityPositiveAtlasCompatible_positive_infinity hπ data D s hs hstart hk hp hpos F w i
    (by omega) (by omega)

/-- Every original chart is compatible with the redundant initial chart. -/
theorem zeroEqualityPositiveAtlasCompatible_initial (i : Fin (s + 1 + 3)) :
    C i ⟨s + 3, by omega⟩ :=
  zeroEqualityPositiveAtlasCompatible_initial_of_infinity hπ data D s hs hstart hk hp hpos F w i
    (zeroEqualityPositiveAtlasCompatible_infinity hπ data D s hs hstart hk hp hpos F w i)

/-- Full original-atlas compatibility follows once the adjacent noninitial equations are proved. -/
theorem zeroEqualityPositiveAtlasCompatible_of_adjacent
    (H : ∀ i j : Fin (s + 1 + 3), 1 ≤ i.val → j.val = i.val + 1 →
      j.val ≤ s + 2 → C i j) : ∀ i j, C i j := by
  have ordered : ∀ i j : Fin (s + 1 + 3), i.val ≤ j.val → C i j := by
    intro i j hij
    by_cases hi0 : i = 0
    · subst i
      exact zeroEqualityPositiveAtlasCompatible_symm hπ data D s hs hstart hk hp hpos F w
        (zeroEqualityPositiveAtlasCompatible_infinity hπ data D s hs hstart hk hp hpos F w j)
    by_cases hjlast : j = ⟨s + 3, by omega⟩
    · rw [hjlast]
      exact zeroEqualityPositiveAtlasCompatible_initial hπ data D s hs hstart hk hp hpos F w i
    by_cases he : i = j
    · subst j
      exact zeroEqualityPositiveAtlasCompatible_self hπ data D s hs hstart hk hp hpos F w i
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
      exact zeroEqualityPositiveAtlasCompatible_terminal_nonadjacent
        hπ data D s hs hk hp hstart hpos F w j (by simpa using hgap)
    have hi2 : 2 ≤ i.val := by
      have h : i.val ≠ 1 := fun h => hi1 (Fin.ext h)
      omega
    exact zeroEqualityPositiveAtlasCompatible_symm hπ data D s hs hstart hk hp hpos F w
      (zeroEqualityPositiveAtlasCompatible_nonadjacent hπ data D s hs hstart hk hp hpos F w
        i j hi2 hgap)
  intro i j
  rcases le_total i.val j.val with hij | hji
  · exact ordered i j hij
  · exact zeroEqualityPositiveAtlasCompatible_symm hπ data D s hs hstart hk hp hpos F w
      (ordered j i hji)

/-- The remaining adjacent equations are exactly the outstanding condition for global descent. -/
theorem zeroEqualityPositiveAtlasCompatible_iff_adjacent :
    (∀ i j, C i j) ↔ ∀ i j : Fin (s + 1 + 3),
      1 ≤ i.val → j.val = i.val + 1 → j.val ≤ s + 2 → C i j := by
  constructor
  · intro H i j _ _ _
    exact H i j
  · exact zeroEqualityPositiveAtlasCompatible_of_adjacent hπ data D s hs hstart hk hp hpos F w

end FLT.Mazur.WeierstrassDividedDepth
