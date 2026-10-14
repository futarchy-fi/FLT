/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitRetainedAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedPositiveSplitAtlasCompatibility

import all FLT.Mazur.WeierstrassDividedPositiveSplitRetainedAtlasCompatibility


/-!
# All adjacent retained pairs in the positive-start strict atlas

The full tensor overlap equations now cover every consecutive retained index.
The first retained pair and the terminal neighbor are included.
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
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "m" => globalTensorAtlasMap hπ data K (s + 1) hs
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 5) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "d" => positiveSplitCycleAtlasFamily hπ data D s hs hstart hk hp F w

local notation "C" => PositiveSplitAtlasCompatible hπ data D s hs hstart hk hp F w

/-- All adjacent retained indices agree, including the first pair and the terminal neighbor. -/
theorem positiveSplitAtlasCompatible_retained_adjacent
    (i j : Fin (s + 1 + 3)) (hi : 2 ≤ i.val) (hij : j.val = i.val + 1)
    (hj : j.val ≤ s + 2) : C i j := by
  let k : Fin (s + 1) := ⟨s + 2 - j.val, by omega⟩
  have hk' : k.val + 1 < s + 1 := by dsimp [k]; omega
  have H := positiveSplitAtlasCompatible_retained_neighbors
    hπ data D s hs hstart hk hp k hk' F w
  have hj' : (⟨s - k.val + 2, by omega⟩ : Fin (s + 1 + 3)) = j :=
    Fin.ext (by dsimp [k]; omega)
  have hi' : (⟨s - (k.val + 1) + 2, by omega⟩ : Fin (s + 1 + 3)) = i :=
    Fin.ext (by dsimp [k]; omega)
  rw [hj', hi'] at H
  exact positiveSplitAtlasCompatible_symm hπ data D s hs hstart hk hp F w H

end FLT.Mazur.WeierstrassDividedDepth
