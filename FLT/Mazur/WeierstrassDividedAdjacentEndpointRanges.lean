/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineMapEndpointRange
public import FLT.Mazur.WeierstrassDividedAdjacentComponentRanges
public import FLT.Mazur.WeierstrassDividedFinalAdjacentComponents
public import FLT.Mazur.WeierstrassDividedRetainedLineAt

/-!
# Full adjacent components as an original line and a retained node

The formula includes scale one and preserves both original endpoint orientations.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- Equal full images remain equal after any common scheme postcomposition. -/
theorem componentRange_postcomp_eq {A B X Y : Scheme.{u}} (f : A ⟶ X) (g : B ⟶ X)
    (t : X ⟶ Y) (h : Set.range f = Set.range g) :
    Set.range (f ≫ t) = Set.range (g ≫ t) := by
  change Set.range (t ∘ f) = Set.range (t ∘ g)
  rw [Set.range_comp, Set.range_comp, h]

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth)
local notation "K" => ResidueField R

/-- Numerical target transport preserves the entire fixed-stage line. -/
@[reassoc] theorem retainedLineAt_index_transport {a b : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (he : a = b) (j : ℕ) (hj : j + 1 ≤ a)
    (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth) (i : Fin 2) :
    retainedLineAt hπ data D a ha j hj hk0 hk i ≫
        eqToHom (finiteGlobalTensorModel_index_congr hπ data K ha hb he) =
      retainedLineAt hπ data D b hb j (by omega) hk0 hk i := by
  subst b
  simp only [eqToHom_refl, Category.comp_id]

/-- The right affine chart is the full original line at the next retained level. -/
theorem orderedAdjacentComponent_right_range (j : ℕ) (hj : j + 1 ≤ n)
    (hk : 2 * (start + j + 1) ≤ depth) (hjNext : j + 2 ≤ n)
    (hkNext : 2 * (start + (j + 1) + 1) ≤ depth) (r : ℕ)
    (hr : j + 2 + r ≤ n) (i : Fin 2) :
    Set.range (ProjectiveLine.right K ≫
        orderedAdjacentComponent hπ data D j hj hk hjNext hkNext r hr i) =
      Set.range (retainedLineAt hπ data D (j + 2 + r) hr (j + 1)
        (by omega) (by omega) hkNext i) := by
  rw [retainedLineAt_original hπ data D (j + 1) hjNext]
  by_cases h : 0 < start + j
  · rw [orderedAdjacentComponent_positive hπ data D j hj hk hjNext hkNext r hr h]
    fin_cases i
    · change Set.range (ProjectiveLine.right K ≫
        adjacentRetainedFirstComponent hπ data D j hj h hk hjNext hkNext r hr) = _
      rw [adjacentRetainedFirstComponent_right, adjacentChartScaling_range]
      rfl
    · change Set.range (ProjectiveLine.right K ≫
        adjacentRetainedSecondComponent hπ data D j hj h hk hjNext hkNext r hr) = _
      rw [adjacentRetainedSecondComponent_right, adjacentChartScaling_range]
      rfl
  · rw [orderedAdjacentComponent_zero_depth hπ data D j hj hk hjNext hkNext r hr (by omega)]
    fin_cases i
    · change Set.range (ProjectiveLine.right K ≫
        adjacentZeroFirstComponent hπ data D j hj (by omega) hk hjNext hkNext r hr) = _
      rw [adjacentZeroFirstComponent_right, adjacentChartScaling_range]
      rfl
    · change Set.range (ProjectiveLine.right K ≫
        adjacentZeroSecondComponent hπ data D j hj (by omega) hk hjNext hkNext r hr) = _
      rw [adjacentZeroSecondComponent_right, adjacentChartScaling_range]
      rfl

variable (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + s + 1) ≤ depth)

/-- Target transport preserves the entire next-line image of each right chart. -/
theorem finalAdjacentComponent_right_range (j : Fin s) (i : Fin 2) :
    Set.range (ProjectiveLine.right K ≫ finalAdjacentComponent hπ data D s hs hk j i) =
      Set.range (retainedLineAt hπ data D (s + 1) hs (j.val + 1)
        (by omega) (by omega) (by omega) i) := by
  unfold finalAdjacentComponent
  rw [← Category.assoc]
  have h := componentRange_postcomp_eq _ _
    (eqToHom (finiteGlobalTensorModel_index_congr hπ data K (by omega) hs (by omega)))
    (orderedAdjacentComponent_right_range hπ data D j.val (by omega) (by omega)
      (by omega) (by omega) (s - (j.val + 1)) (by omega) i)
  rw [retainedLineAt_index_transport hπ data D _ _ (by omega)] at h
  exact h

/-- The next full line and preceding original node exhaust the complete projective component. -/
theorem finalAdjacentComponent_range_line_node (j : Fin s) (i : Fin 2) :
    Set.range (finalAdjacentComponent hπ data D s hs hk j i) =
      Set.range (retainedLineAt hπ data D (s + 1) hs (j.val + 1)
        (by omega) (by omega) (by omega) i) ∪
      Set.range (retainedNodeSectionAt hπ data D (s + 1) hs j.val
        (by omega) (by omega) i) := by
  rw [ProjectiveLine.map_range_right_zero, finalAdjacentComponent_right_range]
  unfold finalAdjacentComponent
  rw [← Category.assoc, orderedAdjacentComponent_zero,
    retainedNodeSectionAt_index_transport hπ data D _ _ (by omega)]

end FLT.Mazur.WeierstrassDividedDepth
