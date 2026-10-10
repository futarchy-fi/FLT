/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentIntegralBoundary
public import FLT.Mazur.WeierstrassDividedOlderGlobalTensorCharts
public import FLT.Mazur.TensorOpenChartCommonBoundary

/-!
# The common boundary in two actual adjacent global tensor charts

The original depth and horizontal transitions identify the complete common
boundary in the first global model containing both retained charts. The
proof uses their integral pushout, without cancellation through a contraction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S]
  (j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
open WeierstrassSuccessiveX
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "f" => data (Fin.mk (j + 2) (Nat.lt_succ_of_le hjNext))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "u" => coord W (π ^ (start + (j + 1))) π
  (Data.b3 f) (Data.b4 f) (Data.b6 f) 2
local notation "a" => depthOverlapEquiv W π (start + j)
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "b" => previousBoundaryEquiv hπ e f
local notation "A" => PrincipalOpenTensor.transitionIso S x t a
local notation "B" => PrincipalOpenTensor.transitionIso S x u b
local notation "i" => olderSuccessiveChart hπ data j hj 1 hjNext
local notation "l" => olderSuccessiveChart hπ data (j + 1) hjNext 0 hjNext

omit [IsBezout R] in
/-- The actual adjacent finite tensor charts retain their full common principal boundary. -/
@[reassoc] theorem adjacentFiniteTensor_boundary :
    (A).inv ≫ PrincipalOpenTensor.inclusion S t ≫
      olderSuccessiveTensorChart hπ data j hj 1 hjNext S =
    (B).inv ≫ PrincipalOpenTensor.inclusion S u ≫
      olderSuccessiveTensorChart hπ data (j + 1) hjNext 0 hjNext S :=
  TensorOpenChart.common_boundary S x t u a b (finiteStructure hπ data (j + 2) hjNext)
    i l (olderSuccessiveChart_structure hπ data j hj 1 hjNext)
      (olderSuccessiveChart_structure hπ data (j + 1) hjNext 0 hjNext)
        (adjacentIntegral_localizations hπ data j hj hjNext)

/-- Both retained embeddings have the same entire boundary in their first common global model. -/
@[reassoc] theorem adjacentGlobalTensor_boundary :
    (A).inv ≫ PrincipalOpenTensor.inclusion S t ≫
      olderGlobalTensorChart hπ data S j hj 1 hjNext =
    (B).inv ≫ PrincipalOpenTensor.inclusion S u ≫
      olderGlobalTensorChart hπ data S (j + 1) hjNext 0 hjNext := by
  exact adjacentFiniteTensor_boundary_assoc hπ data S j hj hjNext
    (finiteLocalTensorEmbedding hπ data S (j + 2) hjNext)

end FLT.Mazur.WeierstrassDividedDepth
