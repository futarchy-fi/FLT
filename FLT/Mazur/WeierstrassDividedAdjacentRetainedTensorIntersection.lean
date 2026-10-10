/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentRetainedTensor
public import FLT.Mazur.WeierstrassDividedAdjacentRetainedIntersection
public import FLT.Mazur.TensorOpenChartCommonIntersection
public import FLT.Mazur.WeierstrassDividedLocalizedIntersection

/-!
# Full adjacent intersections after coefficient extension

The original common boundary is the complete intersection of adjacent
retained tensor charts, both in the local and in the global model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S]
  (j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (r : ℕ) (hr : j + 2 + r ≤ n)
open WeierstrassSuccessiveX
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "f" => data (Fin.mk (j + 2) (Nat.lt_succ_of_le hjNext))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "u" => coord W (π ^ (start + (j + 1))) π
  (Data.b3 f) (Data.b4 f) (Data.b6 f) 2
local notation "depthEquiv" => depthOverlapEquiv W π (start + j)
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "previousEquiv" => previousBoundaryEquiv hπ e f
local notation "A" => PrincipalOpenTensor.transitionIso S x t depthEquiv
local notation "B" => PrincipalOpenTensor.transitionIso S x u previousEquiv
local notation "i" => adjacentRetainedOldChart hπ data j hj r hr
local notation "l" => olderSuccessiveChart hπ data (j + 1) hjNext r hr
local notation "fBase" => finiteStructure hπ data (j + 2 + r) hr

/-- The complete local tensor intersection retains the two original boundary maps. -/
theorem adjacentRetainedFiniteTensor_isPullback :
    IsPullback ((A).inv ≫ PrincipalOpenTensor.inclusion S t)
      ((B).inv ≫ PrincipalOpenTensor.inclusion S u)
      (adjacentRetainedOldTensorChart hπ data S j hj r hr)
      (olderSuccessiveTensorChart hπ data (j + 1) hjNext r hr S) := by
  apply TensorOpenChart.common_boundary_isPullback S x t u depthEquiv previousEquiv
    fBase i l (adjacentRetainedOldChart_structure hπ data j hj r hr)
      (olderSuccessiveChart_structure hπ data (j + 1) hjNext r hr)
  exact localizedBoundary_isPullback hπ e f i l
    (adjacentRetainedIntegral_isPullback hπ data j hj hjNext r hr)

variable [IsBezout R]

/-- The local-to-global open embedding introduces no additional intersection. -/
theorem adjacentRetainedGlobalTensor_isPullback :
    IsPullback ((A).inv ≫ PrincipalOpenTensor.inclusion S t)
      ((B).inv ≫ PrincipalOpenTensor.inclusion S u)
      (adjacentRetainedOldGlobalTensorChart hπ data S j hj r hr)
      (olderGlobalTensorChart hπ data S (j + 1) hjNext r hr) := by
  exact IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _
    (finiteLocalTensorEmbedding hπ data S (j + 2 + r) hr)
    (adjacentRetainedFiniteTensor_isPullback hπ data S j hj hjNext r hr).cone
    (adjacentRetainedFiniteTensor_isPullback hπ data S j hj hjNext r hr).isLimit)

/-- The complete global fiber product is the original principal tensor boundary. -/
def adjacentRetainedGlobalTensorPullbackIso :=
  (adjacentRetainedGlobalTensor_isPullback hπ data S j hj hjNext r hr).isoPullback

/-- The global intersection isomorphism preserves the older boundary projection. -/
@[reassoc] theorem adjacentRetainedGlobalTensorPullbackIso_old :
    (adjacentRetainedGlobalTensorPullbackIso hπ data S j hj hjNext r hr).hom ≫
      pullback.fst _ _ = (A).inv ≫ PrincipalOpenTensor.inclusion S t :=
  (adjacentRetainedGlobalTensor_isPullback hπ data S j hj hjNext r hr).isoPullback_hom_fst

/-- The global intersection isomorphism preserves the newer boundary projection. -/
@[reassoc] theorem adjacentRetainedGlobalTensorPullbackIso_next :
    (adjacentRetainedGlobalTensorPullbackIso hπ data S j hj hjNext r hr).hom ≫
      pullback.snd _ _ = (B).inv ≫ PrincipalOpenTensor.inclusion S u :=
  (adjacentRetainedGlobalTensor_isPullback hπ data S j hj hjNext r hr).isoPullback_hom_snd

end FLT.Mazur.WeierstrassDividedDepth
