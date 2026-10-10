/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentNormalizedIntersection
public import FLT.Mazur.WeierstrassSuccessiveXResidueBoundaryDisjoint
public import FLT.Mazur.WeierstrassDividedRetainedLineAt
public import FLT.Mazur.WeierstrassDividedFinalNodeNonadjacent

/-!
# Full retained horizontal lines exclude all later charts

The original next-depth boundary vanishes on the entire horizontal line.
The exact adjacent pullback then excludes the line from every later chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth)
local notation "K" => ResidueField R
section Adjacent
variable (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
  (hjNext : j + 2 ≤ n)
  (r : ℕ) (hr : j + 2 + r ≤ n)
open WeierstrassSuccessiveX
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "g" => adjacentRetainedOldGlobalTensorChart hπ data K j hj r hr
local notation "gNext" => olderGlobalTensorChart hπ data K (j + 1) hjNext r hr
local notation "E" => residueConicBoundaryIso D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)

variable (v : ResidueField R) (hv : v * (v + residue R W.a₁) = 0)
local notation "L" => residueSuccessiveLineImmersion D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) v hv

/-- The entire horizontal line, not just its node, misses the next global chart. -/
theorem adjacentRetainedLine_next_disjoint :
    Disjoint (Set.range (L ≫ g)) (Set.range gNext) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback
    (adjacentRetainedNormalized_isPullback hπ data D j hj hk0 hk hjNext r hr)
    (L a) b (ha.trans hb.symm)
  obtain ⟨q, _, _⟩ := Scheme.exists_preimage_of_isPullback
    (residueLineBoundary_isPullback D (start + j) hk0 hk
      (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) v hv)
    ((E).hom w) a hw
  exact isEmptyElim q

/-- Reassociation preserves each original line as a dependent morphism. -/
theorem adjacentRetainedLine_original :
    HEq (L ≫ olderGlobalTensorChart hπ data K j hj (r + 1) (by omega)) (L ≫ g) := by
  exact heq_comp rfl rfl
    (finiteGlobalTensorModel_index_congr hπ data K (by omega) hr (by omega)) HEq.rfl
    (adjacentRetainedOldGlobalTensorChart_heq hπ data K j hj r hr)

end Adjacent

/-- A numeric equality retains each line as the same dependent morphism. -/
theorem retainedLineAt_heq (t : ℕ) (ht : t ≤ n) (a : ℕ) (ha : a + 1 ≤ t)
    (r : ℕ) (hr : a + 1 + r ≤ n) (he : a + 1 + r = t)
    (hpos : 0 < start + a) (hdepth : 2 * (start + a + 1) ≤ depth) (i : Fin 2) :
    HEq (retainedLineAt hπ data D t ht a ha hpos hdepth i)
      (Fin.cases (motive := fun _ => ProjectiveLine.chart K ⟶
        finiteGlobalTensorModel hπ data K (a + 1 + r) hr)
        (olderGlobalMiddleFirstLine hπ data D a (by omega) r hr hpos hdepth)
        (fun _ => olderGlobalMiddleSecondLine hπ data D a (by omega) r hr hpos hdepth) i) := by
  subst t
  rw [retainedLineAt_original hπ data D a (by omega)]

/-- Each ordered full line misses the next chart in the fixed-stage model. -/
theorem retainedLineAt_next_disjoint (t : ℕ) (ht : t ≤ n) (a : ℕ)
    (ha : a + 2 ≤ t) (hpos : 0 < start + a)
    (hdepth : 2 * (start + a + 1) ≤ depth) (i : Fin 2) :
    Disjoint (Set.range (retainedLineAt hπ data D t ht a (by omega) hpos hdepth i))
      (Set.range (retainedTensorChartAt hπ data t ht (a + 1) (by omega))) := by
  obtain ⟨r, rfl⟩ : ∃ r, t = a + 2 + r := ⟨t - (a + 2), by omega⟩
  rw [retainedTensorChartAt_original hπ data (a + 1) (by omega)]
  have he := retainedLineAt_heq hπ data D (a + 2 + r) ht a (by omega)
    (r + 1) (by omega) (by omega) hpos hdepth i
  fin_cases i
  · have hmap := eq_of_heq (he.trans
      (adjacentRetainedLine_original hπ data D a (by omega) hpos hdepth r ht
        0 (WeierstrassSuccessiveX.middle_first_root (W.map (residue R)))))
    rw [hmap]
    exact adjacentRetainedLine_next_disjoint hπ data D a (by omega) hpos hdepth
      (by omega) r ht _ _
  · have hmap := eq_of_heq (he.trans
      (adjacentRetainedLine_original hπ data D a (by omega) hpos hdepth r ht
        _ (WeierstrassSuccessiveX.middle_second_root (W.map (residue R)))))
    rw [hmap]
    exact adjacentRetainedLine_next_disjoint hπ data D a (by omega) hpos hdepth
      (by omega) r ht _ _

/-- Every later retained chart is disjoint from the original ordered full line. -/
theorem retainedLineAt_later_disjoint (t : ℕ) (ht : t ≤ n) (a b : ℕ)
    (hab : a < b) (hb : b + 1 ≤ t) (hpos : 0 < start + a)
    (hdepth : 2 * (start + a + 1) ≤ depth) (i : Fin 2) :
    Disjoint (Set.range (retainedLineAt hπ data D t ht a (by omega) hpos hdepth i))
      (Set.range (retainedTensorChartAt hπ data t ht b hb)) := by
  by_cases he : b = a + 1
  · subst b
    exact retainedLineAt_next_disjoint hπ data D t ht a (by omega) hpos hdepth i
  · exact (retainedTensorChartAt_nonadjacent_disjoint hπ data D t ht a b
      (by omega) hb).mono_left (retainedLineAt_range hπ data D t ht a
        (by omega) hpos hdepth i)

end FLT.Mazur.WeierstrassDividedDepth
