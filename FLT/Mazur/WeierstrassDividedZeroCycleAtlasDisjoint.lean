/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNonadjacentGlobalIntersection
public import FLT.Mazur.WeierstrassDividedOlderResidueInfinity

/-!
# Empty intersections at the fixed cyclic atlas indices

The original nonadjacent-chart and positive-depth infinity exclusions are
transported to one fixed finite atlas. No componentwise point criterion is used.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S]

/-- Equal stages and index values preserve disjointness of the actual global chart images. -/
theorem globalTensorAtlas_disjoint_index_congr {a b : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (he : a = b)
    (i j : Fin (a + 3)) (k l : Fin (b + 3))
    (hi : i.val = k.val) (hj : j.val = l.val) :
    Disjoint (Set.range (globalTensorAtlasMap hπ data S a ha i))
        (Set.range (globalTensorAtlasMap hπ data S a ha j)) ↔
      Disjoint (Set.range (globalTensorAtlasMap hπ data S b hb k))
        (Set.range (globalTensorAtlasMap hπ data S b hb l)) := by
  subst b
  have hi' : i = k := Fin.ext hi
  have hj' : j = l := Fin.ext hj
  subst k l
  rfl

variable [IsLocalRing R] {depth : ℕ} (D : SplitNodeDepth W π depth)
  (s : ℕ) (hs : s + 1 ≤ n)
local notation "K" => ResidueField R
local notation "m" => globalTensorAtlasMap hπ data K (s + 1) hs
include D

/-- All separated retained atlas indices, including the initial chart, have empty overlap. -/
theorem zeroSplitCycleAtlas_nonadjacent_disjoint (i k : Fin (s + 1 + 3))
    (hi : 2 ≤ i.val) (hik : i.val + 2 ≤ k.val) :
    Disjoint (Set.range (m k)) (Set.range (m i)) := by
  have hS : algebraMap R K π = 0 := (residue_eq_zero_iff π).mpr
    (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
  let j := s + 1 - i.val
  let r := i.val - 2
  have he : j + 2 + r = s + 1 := by dsimp [j, r]; omega
  let a : Fin (j + 1) := ⟨k.val - i.val - 2, by dsimp [j]; omega⟩
  have H := nonadjacentGlobalTensorAtlas_disjoint hπ data K j (by dsimp [j]; omega)
    (by dsimp [j]; omega) r (by omega) a hS
  exact (globalTensorAtlas_disjoint_index_congr hπ data K (by omega) hs he
    _ _ k i (by dsimp [a, r]; omega) (by dsimp [r]; omega)).mp H

/-- Every positive-depth retained chart misses the entire original infinity chart. -/
theorem zeroSplitCycleAtlas_positive_infinity_disjoint (i : Fin (s + 1 + 3))
    (hi : 2 ≤ i.val) (hil : i.val ≤ s + 1) :
    Disjoint (Set.range (m i)) (Set.range (m 0)) := by
  let j := s + 2 - i.val
  let r := i.val - 2
  have he : j + 1 + r = s + 1 := by dsimp [j, r]; omega
  have H := olderSplitNode_infinity_disjoint hπ data j (by dsimp [j]; omega)
    r (by omega) (by dsimp [j]; omega) D
  exact (globalTensorAtlas_disjoint_index_congr hπ data K (by omega) hs he
    _ _ i 0 (by dsimp [r]; omega) rfl).mp H

/-- Nonadjacent intersections are empty as schemes, not only disjoint component sets. -/
theorem zeroSplitCycleAtlas_nonadjacent_isEmpty (i k : Fin (s + 1 + 3))
    (hi : 2 ≤ i.val) (hik : i.val + 2 ≤ k.val) :
    IsEmpty (Limits.pullback (m k) (m i) : Scheme) :=
  Scheme.isEmpty_pullback _ _ (zeroSplitCycleAtlas_nonadjacent_disjoint hπ data D s hs i k hi hik)

/-- The full positive-depth/infinity fiber product is empty. -/
theorem zeroSplitCycleAtlas_positive_infinity_isEmpty (i : Fin (s + 1 + 3))
    (hi : 2 ≤ i.val) (hil : i.val ≤ s + 1) :
    IsEmpty (Limits.pullback (m i) (m 0) : Scheme) :=
  Scheme.isEmpty_pullback _ _
    (zeroSplitCycleAtlas_positive_infinity_disjoint hπ data D s hs i hi hil)

end FLT.Mazur.WeierstrassDividedDepth
