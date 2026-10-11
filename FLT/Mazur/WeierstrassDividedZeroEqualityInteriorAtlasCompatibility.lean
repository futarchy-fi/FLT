/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityInteriorTensorCompatibility
public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroEqualityInteriorTensorCompatibility
public import FLT.Mazur.WeierstrassDividedZeroEqualityAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroEqualityAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroCyclePositiveTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityInteriorTensorDesc
import all FLT.Mazur.WeierstrassDividedAdjacentRetainedTensor
import all FLT.Mazur.WeierstrassDividedOlderGlobalTensorCharts
import all FLT.Mazur.WeierstrassDividedTensorAtlasComparison
import all FLT.Mazur.WeierstrassDividedGlobalTensorAtlas
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositiveAtlasFamily

/-!
# Full adjacent interior equality-cycle compatibility at the fixed original atlas indices

The compatibility on the entire tensor intersection transports through the
original source isomorphisms and numerical equality of the global stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open Limits

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth) (hpos : 0 < s) (j : Fin s)
local notation "K" => ResidueField R
variable (hj : j.val + 1 < s - 1)
local notation "nextJ" => (Fin.mk (j.val + 1) (by omega) : Fin s)
local notation "r" => s - (j.val + 2)
local notation "g" => adjacentRetainedOldGlobalTensorChart hπ data K
  (j.val + 1) (by omega) r (by omega)
local notation "gNext" => olderGlobalTensorChart hπ data K
  ((j.val + 1) + 1) (by omega) r (by omega)
local notation "m" => globalTensorAtlasMap hπ data K (s + 1) hs
local notation "i" => (Fin.mk (s - j.val + 1) (by omega) : Fin (s + 1 + 3))
local notation "iNext" => (Fin.mk (s - (j.val + 1) + 1) (by omega) : Fin (s + 1 + 3))
local notation "V" => zeroSplitCyclePositiveAtlasIso hπ data s hs j
local notation "N" => zeroSplitCyclePositiveAtlasIso hπ data s hs nextJ

variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 2) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ index, ProjectiveLine.zero (ResidueField R) ≫ F index =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) index))
local notation "d" => zeroEqualityPositiveCycleAtlasFamily hπ data D s hs hstart hk hp hpos F w

include hj in
/-- The complete actual intersection of neighboring positive indexed charts is compatible. -/
theorem zeroEqualityPositiveAtlasCompatible_interior_neighbors :
    ZeroEqualityPositiveAtlasCompatible hπ data D s hs hstart hk hp hpos F w i iNext := by
  apply pullback_compatible_of_source_isos
    (X := finiteGlobalTensorModel hπ data K ((j.val + 1) + 2 + r) (by omega))
    V N g gNext (m i) (m iNext) (d i) (d iNext)
    (finiteGlobalTensorModel_index_congr hπ data K hs (by omega) (by omega))
  · rw [zeroSplitCyclePositiveAtlasIso_global]
    apply (comp_eqToHom_heq _ _).trans
    exact (olderGlobalTensorChart_retention_heq hπ data (j.val + 1) (by omega)
      (s - (j.val + 1)) (r + 1) (by omega) (by omega) (by omega)).trans
        (adjacentRetainedOldGlobalTensorChart_heq hπ data K
          (j.val + 1) (by omega) r (by omega))
  · rw [zeroSplitCyclePositiveAtlasIso_global]
    exact comp_eqToHom_heq _ _
  · have H := zeroEqualityCycleInteriorTensorDesc_compatible
      hπ data D s hs hstart hk hp hpos ⟨j.val, by omega⟩ hj r (by dsimp; omega) F w
    simpa only [zeroEqualityCycleInteriorTensorDesc, Category.assoc] using H

end FLT.Mazur.WeierstrassDividedDepth
