/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticRetainedBoundaryRange
public import FLT.Mazur.WeierstrassDividedAdjacentRetainedPunctures

/-!
# The complete conic boundary is the next arithmetic retained boundary

The original overlap transition identifies the full geometric open, not only
the residue points admitting an arithmetic lift or either single puncture.
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
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
  (hjNext : j + 2 ≤ n) (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "F" => ResidueField A
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "eNext" => data (Fin.mk (j + 2) (Nat.lt_succ_of_le hjNext))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "t" => WeierstrassSuccessiveX.coord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "v" => WeierstrassSuccessiveX.coord W (π ^ (start + (j + 1))) π
  (Data.b3 eNext) (Data.b4 eNext) (Data.b6 eNext) 2
local notation "I" => PrincipalOpenTensor.transitionIso F x t
  (WeierstrassSuccessiveX.depthOverlapEquiv W π (start + j)
    (Data.b3 e) (Data.b4 e) (Data.b6 e))
local notation "J" => PrincipalOpenTensor.transitionIso F x v (previousBoundaryEquiv hπ e eNext)
local notation "b" => adjacentRetainedConicBoundary hπ data D j hj hk0 hk r hr
local notation "next" => finiteRetainedBoundaryTensorChart A hπ data (j + 1) hjNext r hr F

/-- The entire preceding conic open is exactly the next retained arithmetic open. -/
theorem adjacentRetainedConicBoundary_range_eq_retained : Set.range b = Set.range next := by
  rw [adjacentRetainedConicBoundary, SchemeOpenChartRange.range_iso_comp,
    finiteRetainedBoundaryTensorChart_range]
  have h := congrArg (fun f : _ ⟶ _ => Set.range f)
    (adjacentRetainedGlobalTensor_boundary hπ data F j hj hjNext r hr)
  exact (SchemeOpenChartRange.range_iso_comp (I).symm _).symm.trans
    (h.trans (SchemeOpenChartRange.range_iso_comp (J).symm _))

/-- Reassociating the final index preserves the entire original conic-boundary map. -/
theorem olderConicBoundary_reassociate :
    olderGlobalConicBoundary hπ data D j hj (r + 1) (by omega) hk0 hk ≫
      eqToHom (finiteGlobalTensorModel_index_congr hπ data F (by omega) hr
        (show j + 1 + (r + 1) = j + 2 + r by omega)) = b := by
  apply eq_of_heq
  exact (comp_eqToHom_heq _ _).trans
    (adjacentRetainedConicBoundary_original hπ data D j hj hk0 hk r hr)

/-- In the original older spelling, the full conic open still equals the next boundary. -/
theorem olderConicBoundary_range_eq_next_retained :
    Set.range (olderGlobalConicBoundary hπ data D j hj (r + 1) (by omega) hk0 hk ≫
      eqToHom (finiteGlobalTensorModel_index_congr hπ data F (by omega) hr
        (show j + 1 + (r + 1) = j + 2 + r by omega))) = Set.range next := by
  rw [olderConicBoundary_reassociate,
    adjacentRetainedConicBoundary_range_eq_retained A hπ data D j hj hk0 hk hjNext r hr]

end FLT.Mazur.WeierstrassDividedDepth
