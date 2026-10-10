/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedComponentPairCoverage
public import FLT.Mazur.WeierstrassDividedFinalRetainedConic
public import FLT.Mazur.WeierstrassDividedFinalBranchChains

/-!
# Ordered pairs cover the entire original retained conic

Uniform pair statements include both scale one and positive scale. They refer
to the original conic in the fixed target stage, ready for the cyclic family.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
/-- The complete terminal pair contains its full original retained conic. -/
theorem finalTerminalComponents_conic_range (hp : 2 * (start + j + 1) < depth) :
    Set.range (finalTerminalComponent hπ data D j hj hk hp 0) ∪
        Set.range (finalTerminalComponent hπ data D j hj hk hp 1) =
      Set.range (retainedConicAt hπ data D (j + 1) hj j (by omega) hk) ∪
        Set.range (terminalNodeChart hπ data D (j + 1) hj (by omega) hk hp) := by
  rw [retainedConicAt_original hπ data D j hj 0 hj hk]
  by_cases h : 0 < start + j
  · rw [finalTerminalComponent_positive hπ data D j hj hk hp h,
      finalTerminalComponent_positive hπ data D j hj hk hp h,
      orderedRetainedConic_positive hπ data D j hj 0 hj hk h]
    exact terminalComponents_conic_range hπ data D j hj hk hp h
  · rw [finalTerminalComponent_zero_depth hπ data D j hj hk hp (by omega),
      finalTerminalComponent_zero_depth hπ data D j hj hk hp (by omega),
      orderedRetainedConic_zero hπ data D j hj 0 hj hk (by omega)]
    exact terminalZeroComponents_conic_range hπ data D j hj hk hp (by omega)

variable (r : ℕ) (hr : j + 2 + r ≤ n)
  (hjNext : j + 2 ≤ n) (hkNext : 2 * (start + (j + 1) + 1) ≤ depth)

/-- The complete ordered adjacent pair contains the old conic and both next lines. -/
theorem orderedAdjacentComponents_conic_range :
    Set.range (orderedAdjacentComponent hπ data D j hj hk hjNext hkNext r hr 0) ∪
        Set.range (orderedAdjacentComponent hπ data D j hj hk hjNext hkNext r hr 1) =
      Set.range (retainedConicAt hπ data D (j + 2 + r) hr j (by omega) hk) ∪
        (Set.range (olderGlobalMiddleFirstLine hπ data D (j + 1) hjNext r hr
          (by omega) hkNext) ∪
        Set.range (olderGlobalMiddleSecondLine hπ data D (j + 1) hjNext r hr
          (by omega) hkNext)) := by
  rw [retainedConicAt_adjacent_original hπ data D j hj r hr hk]
  by_cases h : 0 < start + j
  · rw [orderedAdjacentComponent_positive hπ data D j hj hk hjNext hkNext r hr h,
      orderedAdjacentComponent_positive hπ data D j hj hk hjNext hkNext r hr h,
      orderedRetainedConic_positive hπ data D j hj (r + 1) (by omega) hk h]
    exact adjacentRetainedComponents_conic_range hπ data D j hj hk r hr hjNext hkNext h
  · rw [orderedAdjacentComponent_zero_depth hπ data D j hj hk hjNext hkNext r hr (by omega),
      orderedAdjacentComponent_zero_depth hπ data D j hj hk hjNext hkNext r hr (by omega),
      orderedRetainedConic_zero hπ data D j hj (r + 1) (by omega) hk (by omega)]
    exact adjacentZeroComponents_conic_range hπ data D j hj hk r hr hjNext hkNext (by omega)

/-- The preceding full conic is contained in its pair of complete adjacent components. -/
theorem orderedAdjacentComponents_cover_conic :
    Set.range (retainedConicAt hπ data D (j + 2 + r) hr j (by omega) hk) ⊆
      Set.range (orderedAdjacentComponent hπ data D j hj hk hjNext hkNext r hr 0) ∪
        Set.range (orderedAdjacentComponent hπ data D j hj hk hjNext hkNext r hr 1) := by
  exact Set.subset_union_left.trans
    (le_of_eq (orderedAdjacentComponents_conic_range hπ data D j hj hk r hr
      hjNext hkNext).symm)

/-- The next entire middle chart is covered by its conic and the preceding component pair. -/
theorem orderedAdjacentComponents_cover_next_chart :
    Set.range (retainedTensorChartAt hπ data (j + 2 + r) hr (j + 1) (by omega)) ⊆
      Set.range (retainedConicAt hπ data D (j + 2 + r) hr (j + 1) (by omega) hkNext) ∪
        (Set.range (orderedAdjacentComponent hπ data D j hj hk hjNext hkNext r hr 0) ∪
        Set.range (orderedAdjacentComponent hπ data D j hj hk hjNext hkNext r hr 1)) := by
  rw [retainedTensorChartAt_original hπ data (j + 1) hjNext r hr,
    retainedConicAt_original hπ data D (j + 1) hjNext r hr hkNext,
    orderedRetainedConic_positive hπ data D (j + 1) hjNext r hr hkNext (by omega)]
  intro x hx
  rw [← olderGlobalMiddleComponents_cover hπ data D (j + 1) hjNext r hr
    (by omega) hkNext] at hx
  rcases hx with hc | hl
  · exact Or.inl hc
  · exact Or.inr ((orderedAdjacentComponents_conic_range hπ data D j hj hk r hr
      hjNext hkNext).symm ▸ Or.inr hl)

end FLT.Mazur.WeierstrassDividedDepth
