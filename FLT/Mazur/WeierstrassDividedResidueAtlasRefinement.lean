/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderIndexedNodeCover
public import FLT.Mazur.WeierstrassDividedTerminalResidueCharts

/-!
# Simultaneous residue refinement of the entire global atlas

For positive initial depth, every older indexed successive chart is covered
by its two ordered node neighborhoods and the terminal chart by its parity
normal form. Infinity and the separate initial ModificationX chart are retained.
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
  (D : SplitNodeDepth W π depth)
local notation "K" => ResidueField R

/-- Transport the exact older-node cover across a numerical spelling of its stage and index. -/
def olderIndexedNodeCoverAt (j : ℕ) (hj : j + 1 ≤ n) (r : ℕ) (hr : j + 1 + r ≤ n)
    (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
    (s : ℕ) (hs : s ≤ n) (i : Fin (s + 3))
    (he : j + 1 + r = s) (hi : i.val = r + 2) :
    (globalTensorAtlasObject hπ data K s hs i).OpenCover := by
  subst s
  have hb : r + 1 < j + 1 + r + 2 := by clear i hi; omega
  have hi' : i = Fin.succ ⟨r + 1, hb⟩ := Fin.ext hi
  subst i
  exact olderIndexedNodeOpenCover hπ data D j hj r hr hk0 hk

variable (s : ℕ) (hs : s ≤ n) (hstart : 0 < start)
  (hk : 2 * (start + s) ≤ depth)

/-- Every actual global atlas object has its constructed residue refinement. -/
def globalResidueAtlasRefinement (i : Fin (s + 3)) :
    (globalTensorAtlasObject hπ data K s hs i).OpenCover := by
  classical
  by_cases hzero : i = 0
  · exact Scheme.coverOfIsIso (𝟙 _)
  by_cases hone : i = Fin.succ 0
  · subst i
    by_cases hp : 2 * (start + s) = depth
    · exact Scheme.coverOfIsIso
        (terminalLaurentAtlasIso hπ data D s hs (by omega) hk hp).hom
    · exact Scheme.coverOfIsIso
        (terminalNodeAtlasIso hπ data D s hs (by omega) hk (by omega)).hom
  by_cases hlast : i.val = s + 2
  · exact Scheme.coverOfIsIso (𝟙 _)
  have hzero' : i.val ≠ 0 := fun h => hzero (Fin.ext h)
  have hone' : i.val ≠ 1 := fun h => hone (Fin.ext h)
  exact olderIndexedNodeCoverAt hπ data D (s + 1 - i.val) (by omega)
    (i.val - 2) (by omega) (by omega) (by omega) s hs i (by omega) (by omega)

/-- The simultaneous refinements cover the entire projective residue model. -/
def globalResidueRefinedOpenCover : (finiteGlobalTensorModel hπ data K s hs).OpenCover :=
  (globalTensorOpenCover hπ data K s hs).bind
    (globalResidueAtlasRefinement hπ data D s hs hstart hk)

/-- Every point lies in one of these actual normalized or retained chart maps. -/
theorem globalResidueRefinedOpenCover_covers (z : finiteGlobalTensorModel hπ data K s hs) :
    ∃ i x, (globalResidueRefinedOpenCover hπ data D s hs hstart hk).f i x = z :=
  (globalResidueRefinedOpenCover hπ data D s hs hstart hk).exists_eq z

end FLT.Mazur.WeierstrassDividedDepth
