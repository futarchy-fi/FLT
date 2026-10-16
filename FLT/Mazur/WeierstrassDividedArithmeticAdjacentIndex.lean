/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticAtlasIndex
public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentIntersection

/-!
# The adjacent-edge index transport in the original arithmetic atlas

The reverse-depth chart map agrees with the actual older adjacent chart,
including the reassociation of its stage. All statements concern full maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

/-- The arithmetic stage is independent of the presentation of its natural-number index. -/
theorem finiteGlobalArithmeticStage_index_congr {k l : ℕ}
    (hk : k ≤ n) (hl : l ≤ n) (h : k = l) :
    finiteGlobalArithmeticStage hπ data k hk m = finiteGlobalArithmeticStage hπ data l hl m := by
  subst l
  rfl

/-- Pullback symmetry retains its actual morphism when equal stage indices are transported. -/
theorem arithmeticPullbackSymmetry_index_heq {k l : ℕ}
    (hk : k ≤ n) (hl : l ≤ n) (h : k = l) :
    HEq (pullbackSymmetry q (finiteGlobalStructure hπ data k hk)).hom
      (pullbackSymmetry q (finiteGlobalStructure hπ data l hl)).hom := by
  subst l
  rfl

/-- The depth-indexed tensor chart preserves its map under equality of final stage indices. -/
theorem arithmeticRetainedTensorChart_index_heq {k l : ℕ}
    (hk : k ≤ n) (hl : l ≤ n) (h : k = l) (a : ℕ) (ha : a < k) (ha' : a < l) :
    HEq (arithmeticRetainedTensorChart hπ data m k hk a ha)
      (arithmeticRetainedTensorChart hπ data m l hl a ha') := by
  subst l
  rfl

variable (a r : ℕ) (hr : a + 2 + r ≤ n)

/-- The original older arithmetic chart and its adjacent-edge version differ only by indexing. -/
theorem finiteArithmeticAdjacentOldTensorChart_heq :
    HEq (finiteArithmeticOlderTensorChart hπ data m a (by omega) (r + 1) (by omega))
      (finiteArithmeticAdjacentOldTensorChart hπ data m a (by omega) r hr) := by
  apply heq_comp rfl
    (finiteGlobalTensorModel_index_congr hπ data Q (by omega) hr (by omega))
    (finiteGlobalArithmeticStage_index_congr hπ data m (by omega) hr (by omega))
    (adjacentRetainedOldGlobalTensorChart_heq hπ data Q a (by omega) r hr)
  exact arithmeticPullbackSymmetry_index_heq hπ data m (by omega) hr (by omega)

/-- The reverse-depth atlas index is exactly the original older adjacent chart. -/
theorem arithmeticRetainedTensorChart_adjacentOld :
    arithmeticRetainedTensorChart hπ data m (a + 2 + r) hr a (by omega) =
      finiteArithmeticAdjacentOldTensorChart hπ data m a (by omega) r hr := by
  have hi := arithmeticRetainedTensorChart_index_heq hπ data m
    (show a + 1 + (r + 1) ≤ n by omega) hr (by omega) a (by omega) (by omega)
  have he := arithmeticRetainedTensorChart_eq hπ data m (a + 2 + r) hr a
    (by omega) (r + 1) (by omega)
  exact eq_of_heq (hi.symm.trans ((heq_of_eq he).trans
    (finiteArithmeticAdjacentOldTensorChart_heq hπ data m a r hr)))

end FLT.Mazur.WeierstrassDividedDepth
