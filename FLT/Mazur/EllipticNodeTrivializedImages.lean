/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeTrivializedChartGeometry
public import FLT.Mazur.SchemeOpenChartRange
public import FLT.Mazur.WeierstrassDividedTerminalComponentIntersection

/-!
# Arithmetic coordinates preserve the entire terminal geometric images

The odd terminal punctures and the even terminal torus have exactly their
original geometric ranges. Their images are independent of the chosen unit
used for arithmetic trivialization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (r : (ResidueField A)ˣ)
  (j : ℕ) (hj : j ≤ n) (hk0 : 0 < start + j)
local notation "F" => ResidueField A
local notation "s" => nodeLaurentScale D r (start + j)

/-- Positive scaling preserves the full right puncture of the original terminal node. -/
theorem nodeTrivializedPositiveChart_range (hp : 2 * (start + j) < depth) :
    Set.range (nodeTrivializedPositiveChart A hπ data D r j hj hk0 hp) =
      Set.range (PolygonNodeBranches.right F ≫
        terminalNodeChart hπ data D j hj hk0 (by omega) hp) := by
  rw [nodeTrivializedPositiveChart]
  exact SchemeOpenChartRange.range_iso_comp (asIso (Spec.map
    (CommRingCat.ofHom (PolygonScaledReciprocal.scaling s).toRingHom))) _

/-- Negative inversion preserves the full left puncture of the original terminal node. -/
theorem nodeTrivializedNegativeChart_range (hp : 2 * (start + j) < depth) :
    Set.range (nodeTrivializedNegativeChart A hπ data D r j hj hk0 hp) =
      Set.range (PolygonNodeBranches.left F ≫
        terminalNodeChart hπ data D j hj hk0 (by omega) hp) := by
  rw [nodeTrivializedNegativeChart]
  exact SchemeOpenChartRange.range_iso_comp (asIso (Spec.map
    (CommRingCat.ofHom (PolygonScaledReciprocal.reciprocal (-s)).toRingHom))) _

/-- The two arithmetic punctures remain disjoint in the original finite model. -/
theorem nodeTrivializedCharts_disjoint (hp : 2 * (start + j) < depth) :
    Disjoint (Set.range (nodeTrivializedNegativeChart A hπ data D r j hj hk0 hp))
      (Set.range (nodeTrivializedPositiveChart A hπ data D r j hj hk0 hp)) := by
  rw [nodeTrivializedNegativeChart_range, nodeTrivializedPositiveChart_range]
  exact componentRange_disjoint_postcomp _ _
    (terminalNodeChart hπ data D j hj hk0 (by omega) hp)
    (terminalNodeChart hπ data D j hj hk0 (by omega) hp).isOpenEmbedding.injective
    (PolygonNodeBranches.disjoint_ranges F)

/-- At even depth the reciprocal chart covers the whole original divided tensor chart. -/
theorem nodeTrivializedMiddleChart_range (hm : 2 * (start + j) = depth) :
    Set.range (nodeTrivializedMiddleChart A hπ data D r j hj hk0 hm) =
      Set.range (globalDividedTensorChart hπ data F j hj) := by
  rw [nodeTrivializedMiddleChart]
  exact (SchemeOpenChartRange.range_iso_comp (asIso (Spec.map
    (CommRingCat.ofHom (PolygonScaledReciprocal.reciprocal (-s)).toRingHom)))
      (terminalLaurentChart hπ data D j hj hk0 (by omega) hm)).trans
        (terminalLaurentChart_range hπ data D j hj hk0 (by omega) hm)

end FLT.Mazur.WeierstrassDividedDepth
