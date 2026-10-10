/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialZeroSlopeChart
public import FLT.Mazur.WeierstrassDividedOlderZeroIndexedNodeCover
public import FLT.Mazur.WeierstrassDividedResidueAtlasFinite

/-!
# Simultaneous finite residue atlas from starting depth zero

Infinity keeps index zero. The separate initial chart is its entire slope
chart, the retained first chart has both signed full nodes, and subsequent
charts use the positive-depth nodes and the terminal parity normal form.
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

/-- Transport the two signed full first nodes to their exact retained index. -/
def olderZeroIndexedNodeCoverAt (j : ℕ) (hj : j + 1 ≤ n)
    (r : ℕ) (hr : j + 1 + r ≤ n) (hk0 : start + j = 0)
    (hk : 2 * (start + j + 1) ≤ depth) (s : ℕ) (hs : s ≤ n)
    (i : Fin (s + 3)) (he : j + 1 + r = s) (hi : i.val = r + 2) :
    (globalTensorAtlasObject hπ data K s hs i).OpenCover := by
  subst s
  have hb : r + 1 < j + 1 + r + 2 := by clear i hi; omega
  have hi' : i = Fin.succ ⟨r + 1, hb⟩ := Fin.ext hi
  subst i
  exact olderZeroIndexedNodeOpenCover hπ data D j hj r hr hk0 hk

instance olderZeroIndexedNodeCoverAt_finite (j : ℕ) (hj : j + 1 ≤ n)
    (r : ℕ) (hr : j + 1 + r ≤ n) (hk0 : start + j = 0)
    (hk : 2 * (start + j + 1) ≤ depth) (s : ℕ) (hs : s ≤ n)
    (i : Fin (s + 3)) (he : j + 1 + r = s) (hi : i.val = r + 2) :
    Finite (olderZeroIndexedNodeCoverAt hπ data D j hj r hr hk0 hk s hs i he hi).I₀ := by
  subst s
  have hb : r + 1 < j + 1 + r + 2 := by clear i hi; omega
  have hi' : i = Fin.succ ⟨r + 1, hb⟩ := Fin.ext hi
  subst i
  exact inferInstanceAs (Finite (Fin 2))

/-- The complete initial slope chart at any spelling of the last global index. -/
def initialZeroSlopeCoverAt (hdepth : 0 < depth) (hstart : start = 0)
    (s : ℕ) (hs : s ≤ n) (i : Fin (s + 3)) (hi : i.val = s + 2) :
    (globalTensorAtlasObject hπ data K s hs i).OpenCover := by
  have hi' : i = Fin.succ ⟨s + 1, by clear i hi; omega⟩ := Fin.ext hi
  subst i
  exact Scheme.coverOfIsIso (initialZeroSlopeAtlasIso hπ data D hdepth hstart s hs).hom

instance initialZeroSlopeCoverAt_finite (hdepth : 0 < depth) (hstart : start = 0)
    (s : ℕ) (hs : s ≤ n) (i : Fin (s + 3)) (hi : i.val = s + 2) :
    Finite (initialZeroSlopeCoverAt hπ data D hdepth hstart s hs i hi).I₀ := by
  have hi' : i = Fin.succ ⟨s + 1, by clear i hi; omega⟩ := Fin.ext hi
  subst i
  exact inferInstanceAs (Finite PUnit)

variable (s : ℕ) (hs : s ≤ n) (hstart : start = 0) (hpos : 0 < s)
  (hk : 2 * (start + s) ≤ depth)

/-- All residue normal forms simultaneously, including the full first retained chart. -/
def globalZeroResidueAtlasRefinement (i : Fin (s + 3)) :
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
  · exact initialZeroSlopeCoverAt hπ data D (by omega) hstart s hs i hlast
  have hzero' : i.val ≠ 0 := fun h => hzero (Fin.ext h)
  have hone' : i.val ≠ 1 := fun h => hone (Fin.ext h)
  by_cases hfirst : i.val = s + 1
  · exact olderZeroIndexedNodeCoverAt hπ data D 0 (by omega) (i.val - 2)
      (by omega) (by omega) (by omega) s hs i (by omega) (by omega)
  exact olderIndexedNodeCoverAt hπ data D (s + 1 - i.val) (by omega)
    (i.val - 2) (by omega) (by omega) (by omega) s hs i (by omega) (by omega)

instance globalZeroResidueAtlasRefinement_finite (i : Fin (s + 3)) :
    Finite (globalZeroResidueAtlasRefinement hπ data D s hs hstart hpos hk i).I₀ := by
  classical
  unfold globalZeroResidueAtlasRefinement
  split_ifs
  · exact inferInstanceAs (Finite PUnit)
  · subst i
    exact inferInstanceAs (Finite PUnit)
  · subst i
    exact inferInstanceAs (Finite PUnit)
  · infer_instance
  · infer_instance
  · infer_instance

/-- The finite normalized charts cover the actual whole projective residue model. -/
def globalZeroResidueOpenCover : (finiteGlobalTensorModel hπ data K s hs).OpenCover :=
  (globalTensorOpenCover hπ data K s hs).bind
    (globalZeroResidueAtlasRefinement hπ data D s hs hstart hpos hk)

instance globalZeroResidueOpenCover_finite :
    Finite (globalZeroResidueOpenCover hπ data D s hs hstart hpos hk).I₀ := by
  change Finite ((i : Fin (s + 3)) ×
    (globalZeroResidueAtlasRefinement hπ data D s hs hstart hpos hk i).I₀)
  infer_instance

/-- Every refined chart keeps its original indexed global inclusion. -/
theorem globalZeroResidueOpenCover_map (i : Fin (s + 3))
    (a : (globalZeroResidueAtlasRefinement hπ data D s hs hstart hpos hk i).I₀) :
    (globalZeroResidueOpenCover hπ data D s hs hstart hpos hk).f ⟨i, a⟩ =
      (globalZeroResidueAtlasRefinement hπ data D s hs hstart hpos hk i).f a ≫
        globalTensorAtlasMap hπ data K s hs i := rfl

/-- The full first chart and every other normalized chart lose no global points. -/
theorem globalZeroResidueOpenCover_covers (z : finiteGlobalTensorModel hπ data K s hs) :
    ∃ i x, (globalZeroResidueOpenCover hπ data D s hs hstart hpos hk).f i x = z :=
  (globalZeroResidueOpenCover hπ data D s hs hstart hpos hk).exists_eq z

end FLT.Mazur.WeierstrassDividedDepth
