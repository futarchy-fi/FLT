/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityZeroInteriorTensorCompatibility
import all FLT.Mazur.WeierstrassDividedZeroEqualityZeroInteriorTensorCompatibility
public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroEqualityZeroTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityInteriorTensorCompatibility
public import FLT.Mazur.WeierstrassDividedZeroEqualityAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroEqualityAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroEqualityInteriorTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositiveAtlasFamily

/-!
# Equality-cycle initial/interior compatibility on the original atlas

The entire tensor overlap equality transports to the original zero chart and
its first positive neighbor. No additional equations on the cyclic family enter.
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
  (hp : 2 * (start + s + 1) = depth) (hs2 : 1 < s)
local notation "K" => ResidueField R
local notation "firstJ" => (Fin.mk 0 (by omega) : Fin (s - 1))
local notation "r" => s - 1
local notation "g" => adjacentRetainedOldGlobalTensorChart hπ data K 0 (by omega) r (by omega)
local notation "gNext" => olderGlobalTensorChart hπ data K (0 + 1) (by omega) r (by omega)
local notation "m" => globalTensorAtlasMap hπ data K (s + 1) hs
local notation "i" => (Fin.mk (s + 2) (by omega) : Fin (s + 1 + 3))
local notation "iNext" => (Fin.mk (s - Fin.val firstJ + 1) (by omega) : Fin (s + 1 + 3))
local notation "V" => zeroSplitCycleZeroAtlasIso hπ data s hs
local notation "N" => zeroSplitCyclePositiveAtlasIso hπ data s hs (Fin.mk 0 (by omega))

variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 2) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ index, ProjectiveLine.zero (ResidueField R) ≫ F index =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) index))
local notation "d" => zeroEqualityPositiveCycleAtlasFamily
  hπ data D s hs hstart hk hp (by omega) F w

include hs2 in
/-- The complete start-zero and positive neighbor intersection is compatible. -/
theorem zeroEqualityPositiveAtlasCompatible_zero_interior :
    ZeroEqualityPositiveAtlasCompatible hπ data D s hs hstart hk hp (by omega) F w i iNext := by
  apply pullback_compatible_of_source_isos V N g gNext (m i) (m iNext) (d i) (d iNext)
    (finiteGlobalTensorModel_index_congr hπ data K hs (by omega) (by omega))
  · rw [zeroSplitCycleZeroAtlasIso_global]
    apply (comp_eqToHom_heq _ _).trans
    exact (olderGlobalTensorChart_retention_heq hπ data 0 (by omega)
      s (r + 1) (by omega) (by omega) (by omega)).trans
        (adjacentRetainedOldGlobalTensorChart_heq hπ data K 0 (by omega) r (by omega))
  · rw [zeroSplitCyclePositiveAtlasIso_global]
    exact comp_eqToHom_heq _ _
  · have H := zeroEqualityCycleZeroInteriorTensorDesc_compatible
      hπ data D s hs hstart hk hp hs2 r (by omega) F w
    simpa only [zeroEqualityPositiveCycleZeroTensorDesc, zeroEqualityCycleInteriorTensorDesc,
      Category.assoc] using H

end FLT.Mazur.WeierstrassDividedDepth
