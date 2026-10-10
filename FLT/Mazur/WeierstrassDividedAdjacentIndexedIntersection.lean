/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentRetainedTensorIntersection
public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveIndexedMap
import all FLT.Mazur.WeierstrassDividedZeroCyclePositiveIndexedMap
import all FLT.Mazur.WeierstrassDividedGlobalTensorAtlas
import all FLT.Mazur.WeierstrassDividedTensorAtlasComparison
import all FLT.Mazur.WeierstrassDividedOlderGlobalTensorCharts

/-!
# The full adjacent boundary in the original indexed global atlas

Source and target index transports preserve both boundary projections.
Thus the original tensor boundary is the entire fiber product of the
literal adjacent retained atlas maps, at every later finite stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "S" => ResidueField R
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

local notation "oldIndex" => (Fin.mk (r + 3) (by omega) : Fin (j + 2 + r + 3))
local notation "nextIndex" => (Fin.succ (Fin.mk (r + 1) (by omega)))
local notation "m" => globalTensorAtlasMap hπ data S (j + 2 + r) hr
local notation "transport" => eqToIso (globalTensorAtlasObject_index_congr hπ data
  (a := j + 1 + (r + 1)) (by omega) hr (by omega)
  (Fin.succ (Fin.mk (r + 1 + 1) (by omega))) oldIndex (by rfl))

/-- The original older tensor algebra, with only its stage and atlas index reassociated. -/
def adjacentRetainedOldAtlasIso :
    Spec (.of (WeierstrassSuccessiveX.ScalarExtension W (π ^ (start + j)) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e) S)) ≅
        globalTensorAtlasObject hπ data S (j + 2 + r) hr oldIndex := by
  let V := olderSuccessiveTensorAtlasIso hπ data S j hj (r + 1) (by omega)
  exact V.trans transport

/-- The reassociated source isomorphism retains the entire original global map. -/
@[reassoc] theorem adjacentRetainedOldAtlasIso_map :
    (adjacentRetainedOldAtlasIso hπ data j hj r hr).hom ≫ m oldIndex =
      adjacentRetainedOldGlobalTensorChart hπ data S j hj r hr := by
  simp only [adjacentRetainedOldAtlasIso, Iso.trans_hom, eqToIso.hom, Category.assoc]
  rw [globalTensorAtlasMap_index_transport hπ data
    (a := j + 1 + (r + 1)) (by omega) hr (by omega)
    (Fin.succ (Fin.mk (r + 1 + 1) (by omega))) oldIndex rfl,
    ← Category.assoc, olderGlobalTensorChart_eq_index]
  apply eq_of_heq
  exact (comp_eqToHom_heq _ _).trans
    (adjacentRetainedOldGlobalTensorChart_heq hπ data S j hj r hr)

local notation "V" => adjacentRetainedOldAtlasIso hπ data j hj r hr
local notation "N" => olderSuccessiveTensorAtlasIso hπ data S (j + 1) hjNext r hr

/-- The complete boundary maps to the literal older atlas object. -/
def adjacentIndexedBoundaryOld :=
  (A).inv ≫ PrincipalOpenTensor.inclusion S t ≫ (V).hom

/-- Its second original transition maps to the literal next retained object. -/
def adjacentIndexedBoundaryNext :=
  (B).inv ≫ PrincipalOpenTensor.inclusion S u ≫ (N).hom

/-- The full tensor boundary is the actual adjacent indexed atlas fiber product. -/
theorem adjacentIndexedBoundary_isPullback :
    IsPullback (adjacentIndexedBoundaryOld hπ data j hj r hr)
      (adjacentIndexedBoundaryNext hπ data j hj hjNext r hr) (m oldIndex) (m nextIndex) := by
  apply (adjacentRetainedGlobalTensor_isPullback hπ data S j hj hjNext r hr).of_iso
    (Iso.refl _) V N (Iso.refl _)
  · simp only [Iso.refl_hom, Category.id_comp, adjacentIndexedBoundaryOld, Category.assoc]
  · simp only [Iso.refl_hom, Category.id_comp, adjacentIndexedBoundaryNext, Category.assoc]
  · simpa only [Iso.refl_hom, Category.comp_id] using
      (adjacentRetainedOldAtlasIso_map hπ data j hj r hr).symm
  · simpa only [Iso.refl_hom, Category.comp_id] using
      (olderGlobalTensorChart_eq_index hπ data S (j + 1) hjNext r hr).symm

/-- The isomorphism identifies the entire original scheme intersection. -/
def adjacentIndexedBoundaryPullbackIso :=
  (adjacentIndexedBoundary_isPullback hπ data j hj hjNext r hr).isoPullback

/-- The first fiber-product projection is the original older boundary map. -/
@[reassoc] theorem adjacentIndexedBoundaryPullbackIso_old :
    (adjacentIndexedBoundaryPullbackIso hπ data j hj hjNext r hr).hom ≫
      Limits.pullback.fst (m oldIndex) (m nextIndex) =
        adjacentIndexedBoundaryOld hπ data j hj r hr :=
  (adjacentIndexedBoundary_isPullback hπ data j hj hjNext r hr).isoPullback_hom_fst

/-- The second fiber-product projection is the unchanged next boundary map. -/
@[reassoc] theorem adjacentIndexedBoundaryPullbackIso_next :
    (adjacentIndexedBoundaryPullbackIso hπ data j hj hjNext r hr).hom ≫
      Limits.pullback.snd (m oldIndex) (m nextIndex) =
        adjacentIndexedBoundaryNext hπ data j hj hjNext r hr :=
  (adjacentIndexedBoundary_isPullback hπ data j hj hjNext r hr).isoPullback_hom_snd

end FLT.Mazur.WeierstrassDividedDepth
