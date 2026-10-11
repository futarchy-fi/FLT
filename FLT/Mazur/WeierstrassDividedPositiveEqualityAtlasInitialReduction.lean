/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityRetainedAdjacent
public import FLT.Mazur.WeierstrassDividedPositiveEqualityInitialInfinityCompatibility
public import FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalAtlasCompatibility
public import FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasSeparation
import all FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasCompatibility

import all FLT.Mazur.WeierstrassDividedPositiveEqualityRetainedAdjacent

import all FLT.Mazur.WeierstrassDividedPositiveEqualityInitialInfinityCompatibility

import all FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalAtlasCompatibility

import all FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasSeparation

/-!
# Positive-start equality compatibility reduces to one initial overlap

All infinity, terminal, nonadjacent and adjacent retained equations are proved.
Only the original initial chart and its first retained neighbor remain.
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
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "m" => globalTensorAtlasMap hπ data K (s + 1) hs
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 4) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "d" => positiveEqualityCycleAtlasFamily hπ data D s hs hstart hk hp F w

local notation "C" => PositiveEqualityAtlasCompatible hπ data D s hs hstart hk hp F w

/-- Every actual atlas chart is compatible with infinity, including the original initial chart. -/
theorem positiveEqualityAtlasCompatible_infinity (i : Fin (s + 1 + 3)) : C i 0 := by
  by_cases hi0 : i = 0
  · subst i
    exact positiveEqualityAtlasCompatible_self hπ data D s hs hstart hk hp F w 0
  by_cases hi1 : i = Fin.succ 0
  · subst i
    exact positiveEqualityAtlasCompatible_terminal_infinity hπ data D s hs hk hp hstart F w
  by_cases hil : i = ⟨s + 3, by omega⟩
  · subst i
    exact positiveEqualityAtlasCompatible_initial_infinity hπ data D s hs hstart hk hp F w
  have h0 : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
  have h1 : i.val ≠ 1 := fun h => hi1 (Fin.ext h)
  have hl : i.val ≠ s + 3 := fun h => hil (Fin.ext h)
  exact positiveEqualityAtlasCompatible_retained_infinity hπ data D s hs hk hp hstart F w i
    (by omega) (by omega)

/-- The original initial/first-retained overlap is the only remaining global equation. -/
theorem positiveEqualityAtlasCompatible_of_initial_neighbor
    (H : C ⟨s + 2, by omega⟩ ⟨s + 3, by omega⟩) : ∀ i j, C i j := by
  have ordered : ∀ i j : Fin (s + 1 + 3), i.val ≤ j.val → C i j := by
    intro i j hij
    by_cases hi0 : i = 0
    · subst i
      exact positiveEqualityAtlasCompatible_symm hπ data D s hs hstart hk hp F w
        (positiveEqualityAtlasCompatible_infinity hπ data D s hs hstart hk hp F w j)
    by_cases he : i = j
    · subst j
      exact positiveEqualityAtlasCompatible_self hπ data D s hs hstart hk hp F w i
    have hi : 1 ≤ i.val := by
      have h : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
      omega
    have hlt : i.val < j.val := by
      have h : i.val ≠ j.val := fun h => he (Fin.ext h)
      omega
    by_cases hadj : j.val = i.val + 1
    · by_cases hjlast : j.val = s + 3
      · have hi' : i = ⟨s + 2, by omega⟩ := Fin.ext (by dsimp; omega)
        have hj' : j = ⟨s + 3, by omega⟩ := Fin.ext hjlast
        simpa only [hi', hj'] using H
      by_cases hi1 : i.val = 1
      · have hi' : i = Fin.succ 0 := Fin.ext hi1
        have hj' : j = ⟨2, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [hi', hj']
        exact positiveEqualityAtlasCompatible_terminal_neighbor hπ data D s hs hstart hk hp F w
      · exact positiveEqualityAtlasCompatible_retained_adjacent hπ data D s hs hstart hk hp F w
          i j (by omega) hadj (by omega)
    · by_cases hi1 : i = Fin.succ 0
      · subst i
        exact positiveEqualityAtlasCompatible_terminal_nonadjacent
          hπ data D s hs hk hp hstart F w j (by simp only [Fin.val_succ, Fin.val_zero] at *; omega)
      have hi2 : 2 ≤ i.val := by
        have h : i.val ≠ 1 := fun h => hi1 (Fin.ext h)
        omega
      exact positiveEqualityAtlasCompatible_symm hπ data D s hs hstart hk hp F w
        (positiveEqualityAtlasCompatible_nonadjacent hπ data D s hs hstart hk hp F w
          i j hi2 (by omega))
  intro i j
  rcases le_total i.val j.val with hij | hji
  · exact ordered i j hij
  · exact positiveEqualityAtlasCompatible_symm hπ data D s hs hstart hk hp F w (ordered j i hji)

/-- Full compatibility is equivalent to its one outstanding original initial overlap. -/
theorem positiveEqualityAtlasCompatible_iff_initial_neighbor :
    (∀ i j, C i j) ↔ C ⟨s + 2, by omega⟩ ⟨s + 3, by omega⟩ := by
  constructor
  · intro H
    exact H _ _
  · exact positiveEqualityAtlasCompatible_of_initial_neighbor hπ data D s hs hstart hk hp F w

end FLT.Mazur.WeierstrassDividedDepth
