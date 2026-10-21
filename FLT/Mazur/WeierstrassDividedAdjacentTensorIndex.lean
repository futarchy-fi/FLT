/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedTensorIndex
public import FLT.Mazur.WeierstrassDividedAdjacentRetainedTensor

/-!
# The canonical indexed representative of every adjacent retained chart

Reassociate arbitrary later stages while keeping the original tensor source
and its entire global chart map. This works over any coefficient algebra.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (j : ℕ) (hj : j + 1 ≤ n)

/-- Reassociation of the stage number preserves the full indexed retained chart. -/
theorem retainedGlobalTensorChart_stage_heq (k l : ℕ) (hk : k ≤ n) (hl : l ≤ n)
    (hk' : j < k) (hl' : j < l) (h : k = l) :
    HEq (retainedGlobalTensorChart hπ data S k hk j hk')
      (retainedGlobalTensorChart hπ data S l hl j hl') := by
  subst l
  rfl

/-- The adjacent original source has its canonical retained indexed presentation. -/
theorem retainedGlobalTensorChart_adjacent (r : ℕ) (hr : j + 2 + r ≤ n) :
    retainedGlobalTensorChart hπ data S (j + 2 + r) hr j (by omega) =
      adjacentRetainedOldGlobalTensorChart hπ data S j hj r hr := by
  have hi := retainedGlobalTensorChart_eq hπ data S (j + 1) hj j (by omega)
    (r + 1) (by omega)
  have he := adjacentRetainedOldGlobalTensorChart_heq hπ data S j hj r hr
  exact eq_of_heq ((retainedGlobalTensorChart_stage_heq hπ data S j
    (j + 2 + r) (j + 1 + (r + 1)) hr (by omega) (by omega) (by omega)
    (by omega)).trans ((heq_of_eq hi).trans he))

/-- The actual source isomorphism preserves every function on the adjacent global input. -/
@[reassoc] theorem retainedTensorAtlasIso_adjacent_map (r : ℕ) (hr : j + 2 + r ≤ n) :
    (retainedTensorAtlasIso hπ data S (j + 2 + r) hr j (by omega)).hom ≫
      globalTensorAtlasMap hπ data S (j + 2 + r) hr
        (Fin.succ ⟨j + 2 + r - j, by omega⟩) =
      adjacentRetainedOldGlobalTensorChart hπ data S j hj r hr :=
  retainedGlobalTensorChart_adjacent hπ data S j hj r hr

end FLT.Mazur.WeierstrassDividedDepth
