/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalNodeChart
public import FLT.Mazur.WeierstrassDividedOlderGlobalComponentSections
public import FLT.Mazur.WeierstrassDividedOlderGlobalIntersections
public import FLT.Mazur.WeierstrassDividedTerminalComponentIntersection

/-!
# Ordered full horizontal lines at a fixed retained stage

The original lines retain their chart, origin and disjoint tangent ordering.
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

/-- The ordered full lines with only their common target index transported. -/
def retainedLineAt (t : ℕ) (ht : t ≤ n) (j : ℕ) (hj : j + 1 ≤ t)
    (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth) (i : Fin 2) :=
  Fin.cases
    (olderGlobalMiddleFirstLine hπ data D j (by omega) (t - (j + 1)) (by omega) hk0 hk)
    (fun _ => olderGlobalMiddleSecondLine hπ data D j (by omega)
      (t - (j + 1)) (by omega) hk0 hk) i ≫
    eqToHom (finiteGlobalTensorModel_index_congr hπ data K (by omega) ht (by omega))

/-- Writing the stage as its original sum recovers exactly the old line map. -/
theorem retainedLineAt_original (j : ℕ) (hj : j + 1 ≤ n) (r : ℕ)
    (hr : j + 1 + r ≤ n) (hk0 : 0 < start + j)
    (hk : 2 * (start + j + 1) ≤ depth) (i : Fin 2) :
    retainedLineAt hπ data D (j + 1 + r) hr j (by omega) hk0 hk i =
      Fin.cases (olderGlobalMiddleFirstLine hπ data D j hj r hr hk0 hk)
        (fun _ => olderGlobalMiddleSecondLine hπ data D j hj r hr hk0 hk) i := by
  apply eq_of_heq
  refine (comp_eqToHom_heq _ _).trans ?_
  have H (q : ℕ) (hq : j + 1 + q ≤ n) (he : q = r) :
      HEq (Fin.cases (motive := fun _ => ProjectiveLine.chart K ⟶
        finiteGlobalTensorModel hπ data K (j + 1 + q) hq)
        (olderGlobalMiddleFirstLine hπ data D j hj q hq hk0 hk)
        (fun _ => olderGlobalMiddleSecondLine hπ data D j hj q hq hk0 hk) i)
        (Fin.cases (motive := fun _ => ProjectiveLine.chart K ⟶
          finiteGlobalTensorModel hπ data K (j + 1 + r) hr)
          (olderGlobalMiddleFirstLine hπ data D j hj r hr hk0 hk)
          (fun _ => olderGlobalMiddleSecondLine hπ data D j hj r hr hk0 hk) i) := by
    subst q
    rfl
  exact H _ _ (by omega)

/-- Each complete line lies in its original retained tensor chart. -/
theorem retainedLineAt_range (t : ℕ) (ht : t ≤ n) (j : ℕ) (hj : j + 1 ≤ t)
    (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth) (i : Fin 2) :
    Set.range (retainedLineAt hπ data D t ht j hj hk0 hk i) ⊆
      Set.range (retainedTensorChartAt hπ data t ht j hj) := by
  obtain ⟨r, rfl⟩ : ∃ r, t = j + 1 + r := ⟨t - (j + 1), by omega⟩
  rw [retainedLineAt_original hπ data D j (by omega),
    retainedTensorChartAt_original hπ data j (by omega)]
  fin_cases i <;> rintro _ ⟨x, rfl⟩ <;> exact ⟨_, rfl⟩

/-- The origin remains the actual corresponding retained node section. -/
@[reassoc] theorem retainedLineAt_origin (t : ℕ) (ht : t ≤ n) (j : ℕ)
    (hj : j + 1 ≤ t) (hk0 : 0 < start + j)
    (hk : 2 * (start + j + 1) ≤ depth) (i : Fin 2) :
    ProjectiveLine.chartZero K ≫ retainedLineAt hπ data D t ht j hj hk0 hk i =
      retainedNodeSectionAt hπ data D t ht j hj hk i := by
  obtain ⟨r, rfl⟩ : ∃ r, t = j + 1 + r := ⟨t - (j + 1), by omega⟩
  rw [retainedLineAt_original hπ data D j (by omega),
    retainedNodeSectionAt_original hπ data D j (by omega),
    orderedRetainedSection_positive hπ data D j (by omega) r ht hk hk0]
  fin_cases i
  · exact olderGlobalFirstSection_line hπ data D j (by omega) r ht hk0 hk
  · exact olderGlobalSecondSection_line hπ data D j (by omega) r ht hk0 hk

/-- The two ordered lines have disjoint full images at the fixed stage. -/
theorem retainedLineAt_disjoint (t : ℕ) (ht : t ≤ n) (j : ℕ) (hj : j + 1 ≤ t)
    (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth) :
    Disjoint (Set.range (retainedLineAt hπ data D t ht j hj hk0 hk 0))
      (Set.range (retainedLineAt hπ data D t ht j hj hk0 hk 1)) := by
  obtain ⟨r, rfl⟩ : ∃ r, t = j + 1 + r := ⟨t - (j + 1), by omega⟩
  rw [retainedLineAt_original hπ data D j (by omega),
    retainedLineAt_original hπ data D j (by omega)]
  exact olderGlobalMiddleLines_disjoint hπ data D j (by omega) r ht hk0 hk

end FLT.Mazur.WeierstrassDividedDepth
