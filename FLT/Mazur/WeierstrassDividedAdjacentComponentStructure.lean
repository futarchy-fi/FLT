/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOrderedAdjacentComponents
public import FLT.Mazur.WeierstrassDividedAdjacentParameterStructure

/-!
# The full adjacent projective components are over the residue field

The structure equality is checked on both complete affine charts of each
projective line. It therefore retains the actual coefficient structure.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
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
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "p" => pullback.fst q (finiteGlobalStructure hπ data (j + 2 + r) hr)

/-- The first positive-depth component is over the original coefficient field. -/
@[reassoc] theorem adjacentRetainedFirstComponent_structure (hk0 : 0 < start + j) :
    adjacentRetainedFirstComponent hπ data D j hj hk0 hk hjNext hkNext r hr ≫ p =
      ProjectiveLine.toBase K := by
  apply pushout.hom_ext
  · change ProjectiveLine.left K ≫
        adjacentRetainedFirstComponent hπ data D j hj hk0 hk hjNext hkNext r hr ≫ p =
      ProjectiveLine.left K ≫ ProjectiveLine.toBase K
    rw [adjacentRetainedFirstComponent_left_assoc, adjacentRetainedFirstParameter_structure,
      conicZeroAffineIso_structure, ProjectiveLine.left_toBase]
  · change ProjectiveLine.right K ≫
        adjacentRetainedFirstComponent hπ data D j hj hk0 hk hjNext hkNext r hr ≫ p =
      ProjectiveLine.right K ≫ ProjectiveLine.toBase K
    rw [adjacentRetainedFirstComponent_right_assoc, olderGlobalMiddleFirstLine_structure,
      ProjectiveLine.chartScaling_toBase, ProjectiveLine.right_toBase]

/-- The second positive-depth component is over the original coefficient field. -/
@[reassoc] theorem adjacentRetainedSecondComponent_structure (hk0 : 0 < start + j) :
    adjacentRetainedSecondComponent hπ data D j hj hk0 hk hjNext hkNext r hr ≫ p =
      ProjectiveLine.toBase K := by
  apply pushout.hom_ext
  · change ProjectiveLine.left K ≫
        adjacentRetainedSecondComponent hπ data D j hj hk0 hk hjNext hkNext r hr ≫ p =
      ProjectiveLine.left K ≫ ProjectiveLine.toBase K
    rw [adjacentRetainedSecondComponent_left_assoc, adjacentRetainedSecondParameter_structure,
      conicZeroAffineIso_structure, ProjectiveLine.left_toBase]
  · change ProjectiveLine.right K ≫
        adjacentRetainedSecondComponent hπ data D j hj hk0 hk hjNext hkNext r hr ≫ p =
      ProjectiveLine.right K ≫ ProjectiveLine.toBase K
    rw [adjacentRetainedSecondComponent_right_assoc, olderGlobalMiddleSecondLine_structure,
      ProjectiveLine.chartScaling_toBase, ProjectiveLine.right_toBase]

/-- The first scale-one component is over the original coefficient field. -/
@[reassoc] theorem adjacentZeroFirstComponent_structure (hk0 : start + j = 0) :
    adjacentZeroFirstComponent hπ data D j hj hk0 hk hjNext hkNext r hr ≫ p =
      ProjectiveLine.toBase K := by
  apply pushout.hom_ext
  · change ProjectiveLine.left K ≫
        adjacentZeroFirstComponent hπ data D j hj hk0 hk hjNext hkNext r hr ≫ p =
      ProjectiveLine.left K ≫ ProjectiveLine.toBase K
    rw [adjacentZeroFirstComponent_left_assoc, adjacentZeroFirstParameter_structure,
      conicZeroAffineIso_structure, ProjectiveLine.left_toBase]
  · change ProjectiveLine.right K ≫
        adjacentZeroFirstComponent hπ data D j hj hk0 hk hjNext hkNext r hr ≫ p =
      ProjectiveLine.right K ≫ ProjectiveLine.toBase K
    rw [adjacentZeroFirstComponent_right_assoc, olderGlobalMiddleFirstLine_structure,
      ProjectiveLine.chartScaling_toBase, ProjectiveLine.right_toBase]

/-- The second scale-one component is over the original coefficient field. -/
@[reassoc] theorem adjacentZeroSecondComponent_structure (hk0 : start + j = 0) :
    adjacentZeroSecondComponent hπ data D j hj hk0 hk hjNext hkNext r hr ≫ p =
      ProjectiveLine.toBase K := by
  apply pushout.hom_ext
  · change ProjectiveLine.left K ≫
        adjacentZeroSecondComponent hπ data D j hj hk0 hk hjNext hkNext r hr ≫ p =
      ProjectiveLine.left K ≫ ProjectiveLine.toBase K
    rw [adjacentZeroSecondComponent_left_assoc, adjacentZeroSecondParameter_structure,
      conicZeroAffineIso_structure, ProjectiveLine.left_toBase]
  · change ProjectiveLine.right K ≫
        adjacentZeroSecondComponent hπ data D j hj hk0 hk hjNext hkNext r hr ≫ p =
      ProjectiveLine.right K ≫ ProjectiveLine.toBase K
    rw [adjacentZeroSecondComponent_right_assoc, olderGlobalMiddleSecondLine_structure,
      ProjectiveLine.chartScaling_toBase, ProjectiveLine.right_toBase]

/-- The uniform ordered pair preserves the original field structure at every later stage. -/
@[reassoc] theorem orderedAdjacentComponent_structure (i : Fin 2) :
    orderedAdjacentComponent hπ data D j hj hk hjNext hkNext r hr i ≫ p =
      ProjectiveLine.toBase K := by
  by_cases h : 0 < start + j
  · rw [orderedAdjacentComponent_positive hπ data D j hj hk hjNext hkNext r hr h]
    fin_cases i
    · exact adjacentRetainedFirstComponent_structure hπ data D j hj hk hjNext hkNext r hr h
    · exact adjacentRetainedSecondComponent_structure hπ data D j hj hk hjNext hkNext r hr h
  · rw [orderedAdjacentComponent_zero_depth hπ data D j hj hk hjNext hkNext r hr (by omega)]
    fin_cases i
    · exact adjacentZeroFirstComponent_structure hπ data D j hj hk hjNext hkNext r hr (by omega)
    · exact adjacentZeroSecondComponent_structure hπ data D j hj hk hjNext hkNext r hr (by omega)

end FLT.Mazur.WeierstrassDividedDepth
