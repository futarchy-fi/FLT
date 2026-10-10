/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentRetainedIntegral
public import FLT.Mazur.WeierstrassDividedOlderGlobalTensorCharts
public import FLT.Mazur.TensorOpenChartCommonBoundary
public import FLT.Mazur.TensorOpenChartTargetTransport

/-!
# The complete adjacent tensor boundary at every later stage

Both original principal transitions still agree after arbitrary later
retention. The older chart uses only the equality of its target stage index;
its actual tensor map is retained by the canonical pullback construction.
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

omit [IsBezout R] in
/-- The coefficient structure follows transport of the same actual whole model. -/
@[reassoc] theorem finiteStructure_index_transport {a b : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (h : a = b) :
    eqToHom (finiteModification_index_congr hπ data ha hb h) ≫
      finiteStructure hπ data b hb = finiteStructure hπ data a ha := by
  subst b
  simp only [eqToHom_refl, Category.id_comp]

omit [IsBezout R] in
/-- The reassociated older chart retains its entire original coefficient square. -/
@[reassoc] theorem adjacentRetainedOldChart_structure :
    i ≫ fBase = Spec.map (CommRingCat.ofHom (algebraMap R
      (WeierstrassSuccessiveX.Coordinate W (π ^ (start + j)) π
        (Data.b3 e) (Data.b4 e) (Data.b6 e)))) := by
  rw [adjacentRetainedOldChart, Category.assoc,
    finiteStructure_index_transport hπ data (by omega) hr (by omega)]
  exact olderSuccessiveChart_structure hπ data j hj (r + 1) (by omega)

omit [IsBezout R] in
/-- The older original tensor chart with the target stage index reassociated. -/
def adjacentRetainedOldTensorChart :=
  TensorOpenChart.chart (S := S) fBase i
    (adjacentRetainedOldChart_structure hπ data j hj r hr)

omit [IsBezout R] in
/-- Reassociation preserves the entire original tensor chart, not merely its contraction. -/
theorem adjacentRetainedOldTensorChart_heq :
    HEq (olderSuccessiveTensorChart hπ data j hj (r + 1) (by omega) S)
      (adjacentRetainedOldTensorChart hπ data S j hj r hr) := by
  exact TensorOpenChart.chart_target_heq
    (finiteModification_index_congr hπ data (by omega) hr (by omega))
    (finiteStructure hπ data (j + 1 + (r + 1)) (by omega)) fBase
    (finiteStructure_index_transport hπ data _ _ (by omega))
    (olderSuccessiveChart hπ data j hj (r + 1) (by omega))
    (olderSuccessiveChart_structure hπ data j hj (r + 1) (by omega))

/-- The same original older tensor algebra inside the later global coefficient model. -/
def adjacentRetainedOldGlobalTensorChart :=
  adjacentRetainedOldTensorChart hπ data S j hj r hr ≫
    finiteLocalTensorEmbedding hπ data S (j + 2 + r) hr

omit [IsBezout R] in
/-- Equal finite stage indices give the same actual coefficient pullback. -/
theorem finiteTensorModel_index_congr {a b : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (h : a = b) :
    finiteTensorModel hπ data S a ha = finiteTensorModel hπ data S b hb := by
  subst b
  rfl

/-- Equal global stage indices give the same actual global coefficient pullback. -/
theorem finiteGlobalTensorModel_index_congr {a b : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (h : a = b) :
    finiteGlobalTensorModel hπ data S a ha = finiteGlobalTensorModel hπ data S b hb := by
  subst b
  rfl

/-- The original local-to-global embedding does not depend on the stage-index presentation. -/
theorem finiteLocalTensorEmbedding_index_heq {a b : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (h : a = b) :
    HEq (finiteLocalTensorEmbedding hπ data S a ha)
      (finiteLocalTensorEmbedding hπ data S b hb) := by
  subst b
  rfl

/-- The global older chart is the original full map with only its stage index reassociated. -/
theorem adjacentRetainedOldGlobalTensorChart_heq :
    HEq (olderGlobalTensorChart hπ data S j hj (r + 1) (by omega))
      (adjacentRetainedOldGlobalTensorChart hπ data S j hj r hr) := by
  apply heq_comp rfl
    (finiteTensorModel_index_congr hπ data S (by omega) hr (by omega))
    (finiteGlobalTensorModel_index_congr hπ data S (by omega) hr (by omega))
    (adjacentRetainedOldTensorChart_heq hπ data S j hj r hr)
  exact finiteLocalTensorEmbedding_index_heq hπ data S (by omega) hr (by omega)

omit [IsBezout R] in
/-- Every retained finite pair agrees on the whole original tensor boundary. -/
@[reassoc] theorem adjacentRetainedFiniteTensor_boundary :
    (A).inv ≫ PrincipalOpenTensor.inclusion S t ≫
      adjacentRetainedOldTensorChart hπ data S j hj r hr =
    (B).inv ≫ PrincipalOpenTensor.inclusion S u ≫
      olderSuccessiveTensorChart hπ data (j + 1) hjNext r hr S :=
  TensorOpenChart.common_boundary S x t u depthEquiv previousEquiv fBase i l
    (adjacentRetainedOldChart_structure hπ data j hj r hr)
    (olderSuccessiveChart_structure hπ data (j + 1) hjNext r hr)
    (adjacentRetainedIntegral_localizations hπ data j hj hjNext r hr)

/-- The complete adjacent tensor boundaries agree in every later common global model. -/
@[reassoc] theorem adjacentRetainedGlobalTensor_boundary :
    (A).inv ≫ PrincipalOpenTensor.inclusion S t ≫
      adjacentRetainedOldGlobalTensorChart hπ data S j hj r hr =
    (B).inv ≫ PrincipalOpenTensor.inclusion S u ≫
      olderGlobalTensorChart hπ data S (j + 1) hjNext r hr := by
  exact adjacentRetainedFiniteTensor_boundary_assoc hπ data S j hj hjNext r hr
    (finiteLocalTensorEmbedding hπ data S (j + 2 + r) hr)

end FLT.Mazur.WeierstrassDividedDepth
