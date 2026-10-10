/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidueAtlasRefinement

/-!
# Finiteness and maps of the simultaneous residue atlas

The simultaneous node refinements give a finite cover, not just an arbitrary
open cover. Every member retains its map through the original global index.
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

instance olderIndexedNodeCoverAt_finite (j : ℕ) (hj : j + 1 ≤ n)
    (r : ℕ) (hr : j + 1 + r ≤ n)
    (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
    (s : ℕ) (hs : s ≤ n) (i : Fin (s + 3))
    (he : j + 1 + r = s) (hi : i.val = r + 2) :
    Finite (olderIndexedNodeCoverAt hπ data D j hj r hr hk0 hk s hs i he hi).I₀ := by
  subst s
  have hb : r + 1 < j + 1 + r + 2 := by clear i hi; omega
  have hi' : i = Fin.succ ⟨r + 1, hb⟩ := Fin.ext hi
  subst i
  exact inferInstanceAs (Finite (Fin 2))

variable (s : ℕ) (hs : s ≤ n) (hstart : 0 < start)
  (hk : 2 * (start + s) ≤ depth)

instance globalResidueAtlasRefinement_finite (i : Fin (s + 3)) :
    Finite (globalResidueAtlasRefinement hπ data D s hs hstart hk i).I₀ := by
  classical
  unfold globalResidueAtlasRefinement
  split_ifs
  · exact inferInstanceAs (Finite PUnit)
  · subst i
    exact inferInstanceAs (Finite PUnit)
  · subst i
    exact inferInstanceAs (Finite PUnit)
  · exact inferInstanceAs (Finite PUnit)
  · infer_instance

instance globalResidueRefinedOpenCover_finite :
    Finite (globalResidueRefinedOpenCover hπ data D s hs hstart hk).I₀ := by
  change Finite ((i : Fin (s + 3)) ×
    (globalResidueAtlasRefinement hπ data D s hs hstart hk i).I₀)
  infer_instance

/-- Each refined inclusion factors through its original indexed global chart. -/
theorem globalResidueRefinedOpenCover_map
    (i : Fin (s + 3)) (a : (globalResidueAtlasRefinement hπ data D s hs hstart hk i).I₀) :
    (globalResidueRefinedOpenCover hπ data D s hs hstart hk).f ⟨i, a⟩ =
      (globalResidueAtlasRefinement hπ data D s hs hstart hk i).f a ≫
        globalTensorAtlasMap hπ data K s hs i := rfl

end FLT.Mazur.WeierstrassDividedDepth
