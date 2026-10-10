/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialRetainedBoundary
public import FLT.Mazur.WeierstrassDividedOlderGlobalTensorCharts
public import FLT.Mazur.TensorOpenChartCommonBoundary

/-!
# The full initial boundary in the actual retained tensor model

Both original principal transitions agree after base change and all later
retentions. The comparison retains the original initial and first successive charts.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
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

/-- The initial and first successive coefficient charts agree on the full original boundary. -/
@[reassoc] theorem initialRetainedFiniteTensor_boundary :
    (A).inv ≫ PrincipalOpenTensor.inclusion S t ≫ finiteInitialTensorChart hπ data S (1 + r) hr =
      (B).inv ≫ PrincipalOpenTensor.inclusion S u ≫
        olderSuccessiveTensorChart hπ data 0 h1 r hr S :=
  TensorOpenChart.common_boundary S x t u a b (finiteStructure hπ data (1 + r) hr)
    (finiteInitialChart hπ data (1 + r) hr) (olderSuccessiveChart hπ data 0 h1 r hr)
    (finiteInitialChart_structure hπ data (1 + r) hr)
    (olderSuccessiveChart_structure hπ data 0 h1 r hr)
    (initialRetainedIntegral_localizations hπ data h1 r hr)

variable [IsBezout R]

/-- The complete initial tensor overlap still agrees in the actual projective global model. -/
@[reassoc] theorem initialRetainedGlobalTensor_boundary :
    (A).inv ≫ PrincipalOpenTensor.inclusion S t ≫ globalInitialTensorChart hπ data S (1 + r) hr =
      (B).inv ≫ PrincipalOpenTensor.inclusion S u ≫
        olderGlobalTensorChart hπ data S 0 h1 r hr :=
  initialRetainedFiniteTensor_boundary_assoc hπ data S h1 r hr
    (finiteLocalTensorEmbedding hπ data S (1 + r) hr)

end FLT.Mazur.WeierstrassDividedDepth
