/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentParameterOrigins
public import FLT.Mazur.WeierstrassDividedFinalNodeAdjacent

/-!
# Adjacent projective components with both original retained endpoints

The uniform ordered pair includes scale one. Its zero and infinity endpoints
are respectively the preceding and following nodes in the same retained family.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth)
  (hjNext : j + 2 ≤ n) (hkNext : 2 * (start + (j + 1) + 1) ≤ depth)
  (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "K" => ResidueField R

/-- The retained section at an adjacent stage is the original section with index transport. -/
theorem retainedNodeSectionAt_adjacent_original (i : Fin 2) :
    retainedNodeSectionAt hπ data D (j + 2 + r) hr j (by omega) hk i =
      orderedRetainedSection hπ data D j hj (r + 1) (by omega) hk i ≫
        eqToHom (finiteGlobalTensorModel_index_congr hπ data K (by omega) hr
          (show j + 1 + (r + 1) = j + 2 + r by omega)) := by
  apply eq_of_heq
  exact (retainedNodeSectionAt_heq hπ data D (j + 2 + r) hr j (by omega)
    (r + 1) (by omega) (by omega) hk i).trans (comp_eqToHom_heq _ _).symm

/-- Both full adjacent components, in their original tangent order. -/
def orderedAdjacentComponent (i : Fin 2) :
    ProjectiveLine.scheme K ⟶ finiteGlobalTensorModel hπ data K (j + 2 + r) hr :=
  if h : 0 < start + j then
    Fin.cases (adjacentRetainedFirstComponent hπ data D j hj h hk hjNext hkNext r hr)
      (fun _ => adjacentRetainedSecondComponent hπ data D j hj h hk hjNext hkNext r hr) i
  else
    Fin.cases (adjacentZeroFirstComponent hπ data D j hj (by omega) hk hjNext hkNext r hr)
      (fun _ => adjacentZeroSecondComponent hπ data D j hj (by omega) hk hjNext hkNext r hr) i

/-- Positive depth retains the two original complete adjacent gluings. -/
theorem orderedAdjacentComponent_positive (h : 0 < start + j) (i : Fin 2) :
    orderedAdjacentComponent hπ data D j hj hk hjNext hkNext r hr i =
      Fin.cases (adjacentRetainedFirstComponent hπ data D j hj h hk hjNext hkNext r hr)
        (fun _ => adjacentRetainedSecondComponent hπ data D j hj h hk hjNext hkNext r hr) i := by
  simp only [orderedAdjacentComponent, dite_eq_left h]

/-- Scale one retains its original full-node gluings and branch order. -/
theorem orderedAdjacentComponent_zero_depth (h : start + j = 0) (i : Fin 2) :
    orderedAdjacentComponent hπ data D j hj hk hjNext hkNext r hr i =
      Fin.cases (adjacentZeroFirstComponent hπ data D j hj h hk hjNext hkNext r hr)
        (fun _ => adjacentZeroSecondComponent hπ data D j hj h hk hjNext hkNext r hr) i := by
  simp only [orderedAdjacentComponent, dite_eq_right (show ¬0 < start + j by omega)]

/-- Zero is the original preceding ordered node, including at scale one. -/
@[reassoc] theorem orderedAdjacentComponent_zero (i : Fin 2) :
    ProjectiveLine.zero K ≫ orderedAdjacentComponent hπ data D j hj hk hjNext hkNext r hr i =
      retainedNodeSectionAt hπ data D (j + 2 + r) hr j (by omega) hk i := by
  rw [retainedNodeSectionAt_adjacent_original hπ data D j hj hk r hr]
  by_cases h : 0 < start + j
  · rw [orderedAdjacentComponent_positive hπ data D j hj hk hjNext hkNext r hr h,
      orderedRetainedSection_positive hπ data D j hj (r + 1) (by omega) hk h]
    fin_cases i
    · change ProjectiveLine.zero K ≫
        adjacentRetainedFirstComponent hπ data D j hj h hk hjNext hkNext r hr =
          olderGlobalFirstSection hπ data D j hj (r + 1) (by omega) h hk ≫ _
      rw [adjacentRetainedFirstComponent_zero, adjacentRetainedFirstParameter_origin]
    · change ProjectiveLine.zero K ≫
        adjacentRetainedSecondComponent hπ data D j hj h hk hjNext hkNext r hr =
          olderGlobalSecondSection hπ data D j hj (r + 1) (by omega) h hk ≫ _
      rw [adjacentRetainedSecondComponent_zero, adjacentRetainedSecondParameter_origin]
  · rw [orderedAdjacentComponent_zero_depth hπ data D j hj hk hjNext hkNext r hr (by omega),
      orderedRetainedSection_zero hπ data D j hj (r + 1) (by omega) hk (by omega)]
    fin_cases i
    · change ProjectiveLine.zero K ≫
        adjacentZeroFirstComponent hπ data D j hj (by omega) hk hjNext hkNext r hr =
          olderGlobalZeroFirstSection hπ data D j hj (r + 1) (by omega) (by omega) hk ≫ _
      rw [adjacentZeroFirstComponent_zero, adjacentZeroFirstParameter_origin]
    · change ProjectiveLine.zero K ≫
        adjacentZeroSecondComponent hπ data D j hj (by omega) hk hjNext hkNext r hr =
          olderGlobalZeroSecondSection hπ data D j hj (r + 1) (by omega) (by omega) hk ≫ _
      rw [adjacentZeroSecondComponent_zero, adjacentZeroSecondParameter_origin]

/-- Infinity is the matching original ordered node at the next retained level. -/
@[reassoc] theorem orderedAdjacentComponent_infinity (i : Fin 2) :
    ProjectiveLine.infinity K ≫
        orderedAdjacentComponent hπ data D j hj hk hjNext hkNext r hr i =
      retainedNodeSectionAt hπ data D (j + 2 + r) hr (j + 1) (by omega) hkNext i := by
  rw [retainedNodeSectionAt_original hπ data D (j + 1) hjNext r hr hkNext i,
    orderedRetainedSection_positive hπ data D (j + 1) hjNext r hr hkNext (by omega)]
  by_cases h : 0 < start + j
  · rw [orderedAdjacentComponent_positive hπ data D j hj hk hjNext hkNext r hr h]
    fin_cases i
    · exact adjacentRetainedFirstComponent_infinity hπ data D j hj h hk hjNext hkNext r hr
    · exact adjacentRetainedSecondComponent_infinity hπ data D j hj h hk hjNext hkNext r hr
  · rw [orderedAdjacentComponent_zero_depth hπ data D j hj hk hjNext hkNext r hr (by omega)]
    fin_cases i
    · exact adjacentZeroFirstComponent_infinity hπ data D j hj (by omega) hk hjNext hkNext r hr
    · exact adjacentZeroSecondComponent_infinity hπ data D j hj (by omega) hk hjNext hkNext r hr

end FLT.Mazur.WeierstrassDividedDepth
