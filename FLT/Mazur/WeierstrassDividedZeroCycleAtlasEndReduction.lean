/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroCyclePositiveAtlasCompatibility
public import FLT.Mazur.WeierstrassDividedZeroCycleAtlasAdjacentReduction
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasAdjacentReduction
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasFamily

/-!
# Only the two end neighbors remain for the actual cyclic atlas

Every pair of neighboring positive retained charts is now compatible on its
whole scheme intersection. The terminal and start-zero pairs are the only
remaining equations, including their coincidence when there is no middle level.
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

/-- All adjacent positive retained indices have their proved full overlap equality. -/
theorem zeroSplitCycleAtlasCompatible_positive_adjacent (i k : Fin (s + 1 + 3))
    (hi : 2 ≤ i.val) (hik : k.val = i.val + 1) (hk : k.val ≤ s + 1) : C i k := by
  let j : Fin s := ⟨s + 1 - k.val, by omega⟩
  have hj : j.val + 1 < s := by dsimp [j]; omega
  have H := zeroSplitCycleAtlasCompatible_positive_neighbors
    hπ data D s hs hstart hp j hj F w
  have he : (⟨s - j.val + 1, by omega⟩ : Fin (s + 1 + 3)) = k :=
    Fin.ext (by dsimp [j]; omega)
  have hn : (⟨s - (j.val + 1) + 1, by omega⟩ : Fin (s + 1 + 3)) = i :=
    Fin.ext (by dsimp [j]; omega)
  rw [he, hn] at H
  exact zeroSplitCycleAtlasCompatible_symm hπ data D s hs hstart hp F w H

/-- The two end-neighbor equations now suffice for descent of the entire original atlas. -/
theorem zeroSplitCycleAtlasCompatible_of_end_neighbors
    (hterminal : C (Fin.succ 0) ⟨2, by omega⟩)
    (hzero : C ⟨s + 1, by omega⟩ ⟨s + 2, by omega⟩) : ∀ i k, C i k := by
  apply zeroSplitCycleAtlasCompatible_of_adjacent hπ data D s hs hstart hp F w
  intro i k hi hik hk
  by_cases hit : i.val = 1
  · have he : i = Fin.succ 0 := Fin.ext hit
    have hn : k = ⟨2, by omega⟩ := Fin.ext (by dsimp; omega)
    simpa only [he, hn] using hterminal
  by_cases hkz : k.val = s + 2
  · have he : i = ⟨s + 1, by omega⟩ := Fin.ext (by dsimp; omega)
    have hn : k = ⟨s + 2, by omega⟩ := Fin.ext hkz
    simpa only [he, hn] using hzero
  exact zeroSplitCycleAtlasCompatible_positive_adjacent hπ data D s hs hstart hp F w
    i k (by omega) hik (by omega)

/-- Full atlas compatibility is equivalent to exactly the two outstanding end-neighbor pairs. -/
theorem zeroSplitCycleAtlasCompatible_iff_end_neighbors :
    (∀ i k, C i k) ↔
      C (Fin.succ 0) ⟨2, by omega⟩ ∧ C ⟨s + 1, by omega⟩ ⟨s + 2, by omega⟩ := by
  constructor
  · intro H
    exact ⟨H _ _, H _ _⟩
  · rintro ⟨hterminal, hzero⟩
    exact zeroSplitCycleAtlasCompatible_of_end_neighbors
      hπ data D s hs hstart hp F w hterminal hzero

end FLT.Mazur.WeierstrassDividedDepth
