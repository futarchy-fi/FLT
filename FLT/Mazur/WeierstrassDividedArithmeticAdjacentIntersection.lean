/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentRetainedTensorIntersection
public import FLT.Mazur.WeierstrassDividedArithmeticBoundaryCharts

/-!
# Full adjacent intersections in the original arithmetic stages

The complete original tensor boundary is the exact intersection of adjacent
retained charts at every arithmetic order and every later retention depth.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open PolygonArithmeticStages
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m : ℕ)
  (j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (r : ℕ) (hr : j + 2 + r ≤ n)
open WeierstrassSuccessiveX
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
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
local notation "A" => PrincipalOpenTensor.transitionIso Q x t depthEquiv
local notation "B" => PrincipalOpenTensor.transitionIso Q x u previousEquiv
/-- The older arithmetic chart with its retained stage index reassociated. -/
def finiteArithmeticAdjacentOldTensorChart :
    Spec (.of (ScalarExtension W (π ^ (start + j)) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e) Q)) ⟶
        finiteGlobalArithmeticStage hπ data (j + 2 + r) hr m :=
  adjacentRetainedOldGlobalTensorChart hπ data Q j hj r hr ≫
    (pullbackSymmetry q (finiteGlobalStructure hπ data (j + 2 + r) hr)).hom

/-- The older adjacent chart uses the same original arithmetic coefficient morphism. -/
@[reassoc] theorem finiteArithmeticAdjacentOldTensorChart_structure :
    finiteArithmeticAdjacentOldTensorChart hπ data m j hj r hr ≫
      finiteGlobalArithmeticStructure hπ data (j + 2 + r) hr m =
        Spec.map (CommRingCat.ofHom (algebraMap Q
          (ScalarExtension W (π ^ (start + j)) π
            (Data.b3 e) (Data.b4 e) (Data.b6 e) Q))) := by
  change (adjacentRetainedOldGlobalTensorChart hπ data Q j hj r hr ≫
    (pullbackSymmetry q (finiteGlobalStructure hπ data (j + 2 + r) hr)).hom) ≫
      pullback.snd (finiteGlobalStructure hπ data (j + 2 + r) hr) q = _
  simp only [Category.assoc, pullbackSymmetry_hom_comp_snd,
    adjacentRetainedOldGlobalTensorChart, finiteLocalTensorEmbedding_structure,
    adjacentRetainedOldTensorChart, TensorOpenChart.chart_fst]
  rfl

/-- Adjacent retained arithmetic charts have exactly the full original tensor intersection. -/
theorem adjacentArithmeticTensor_isPullback :
    IsPullback ((A).inv ≫ PrincipalOpenTensor.inclusion Q t)
      ((B).inv ≫ PrincipalOpenTensor.inclusion Q u)
      (finiteArithmeticAdjacentOldTensorChart hπ data m j hj r hr)
      (finiteArithmeticOlderTensorChart hπ data m (j + 1) hjNext r hr) :=
  IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _
    (pullbackSymmetry q (finiteGlobalStructure hπ data (j + 2 + r) hr)).hom
    (adjacentRetainedGlobalTensor_isPullback hπ data Q j hj hjNext r hr).cone
    (adjacentRetainedGlobalTensor_isPullback hπ data Q j hj hjNext r hr).isLimit)

/-- The entire original boundary is isomorphic to the adjacent arithmetic fiber product. -/
def adjacentArithmeticTensorPullbackIso :=
  (adjacentArithmeticTensor_isPullback hπ data m j hj hjNext r hr).isoPullback

/-- The intersection comparison retains the original older boundary projection. -/
@[reassoc] theorem adjacentArithmeticTensorPullbackIso_old :
    (adjacentArithmeticTensorPullbackIso hπ data m j hj hjNext r hr).hom ≫
      pullback.fst _ _ = (A).inv ≫ PrincipalOpenTensor.inclusion Q t :=
  (adjacentArithmeticTensor_isPullback hπ data m j hj hjNext r hr).isoPullback_hom_fst

/-- The intersection comparison retains the original newer boundary projection. -/
@[reassoc] theorem adjacentArithmeticTensorPullbackIso_next :
    (adjacentArithmeticTensorPullbackIso hπ data m j hj hjNext r hr).hom ≫
      pullback.snd _ _ = (B).inv ≫ PrincipalOpenTensor.inclusion Q u :=
  (adjacentArithmeticTensor_isPullback hπ data m j hj hjNext r hr).isoPullback_hom_snd

end FLT.Mazur.WeierstrassDividedDepth
