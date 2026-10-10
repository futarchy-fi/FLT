/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialRetainedIntersection
public import FLT.Mazur.WeierstrassDividedOlderGlobalTensorCharts
public import FLT.Mazur.TensorOpenChartCommonIntersection

/-!
# Exact initial chart intersections after coefficient extension

The original initial and first successive tensor charts meet in precisely
their common principal boundary, in every retained finite and global model.
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
  (h1 : 1 ≤ n) (r : ℕ) (hr : 1 + r ≤ n)
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le h1))
local notation "a" => WeierstrassModificationX.overlapEquiv W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "b" => previousBoundaryEquiv hπ d e
local notation "x" => WeierstrassDilatation.x W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "t" => WeierstrassModificationX.t W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "u" => WeierstrassSuccessiveX.coord W (π ^ start) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) 2
local notation "A" => PrincipalOpenTensor.transitionIso S x t a
local notation "B" => PrincipalOpenTensor.transitionIso S x u b

/-- Base change preserves the complete initial/first-successive intersection. -/
theorem initialRetainedFiniteTensor_isPullback :
    IsPullback ((A).inv ≫ PrincipalOpenTensor.inclusion S t)
      ((B).inv ≫ PrincipalOpenTensor.inclusion S u)
      (finiteInitialTensorChart hπ data S (1 + r) hr)
      (olderSuccessiveTensorChart hπ data 0 h1 r hr S) :=
  TensorOpenChart.common_boundary_isPullback S x t u a b
    (finiteStructure hπ data (1 + r) hr)
    (finiteInitialChart hπ data (1 + r) hr) (olderSuccessiveChart hπ data 0 h1 r hr)
    (finiteInitialChart_structure hπ data (1 + r) hr)
    (olderSuccessiveChart_structure hπ data 0 h1 r hr)
    (initialRetainedLocalized_isPullback hπ data h1 r hr)

variable [IsBezout R]

/-- The global open embedding adds no intersection to the two original tensor charts. -/
theorem initialRetainedGlobalTensor_isPullback :
    IsPullback ((A).inv ≫ PrincipalOpenTensor.inclusion S t)
      ((B).inv ≫ PrincipalOpenTensor.inclusion S u)
      (globalInitialTensorChart hπ data S (1 + r) hr)
      (olderGlobalTensorChart hπ data S 0 h1 r hr) :=
  IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _
    (finiteLocalTensorEmbedding hπ data S (1 + r) hr)
    (initialRetainedFiniteTensor_isPullback hπ data S h1 r hr).cone
    (initialRetainedFiniteTensor_isPullback hπ data S h1 r hr).isLimit)

/-- The global intersection is the full original principal tensor boundary. -/
def initialRetainedGlobalTensorPullbackIso :=
  (initialRetainedGlobalTensor_isPullback hπ data S h1 r hr).isoPullback

/-- The exact global intersection retains the original initial projection. -/
@[reassoc] theorem initialRetainedGlobalTensorPullbackIso_initial :
    (initialRetainedGlobalTensorPullbackIso hπ data S h1 r hr).hom ≫
      pullback.fst _ _ = (A).inv ≫ PrincipalOpenTensor.inclusion S t :=
  (initialRetainedGlobalTensor_isPullback hπ data S h1 r hr).isoPullback_hom_fst

/-- The exact global intersection retains the original successive projection. -/
@[reassoc] theorem initialRetainedGlobalTensorPullbackIso_successive :
    (initialRetainedGlobalTensorPullbackIso hπ data S h1 r hr).hom ≫
      pullback.snd _ _ = (B).inv ≫ PrincipalOpenTensor.inclusion S u :=
  (initialRetainedGlobalTensor_isPullback hπ data S h1 r hr).isoPullback_hom_snd

end FLT.Mazur.WeierstrassDividedDepth
