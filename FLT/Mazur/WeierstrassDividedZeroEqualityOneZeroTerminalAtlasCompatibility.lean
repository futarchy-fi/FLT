/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityOneZeroTerminalTensorCompatibility
import all FLT.Mazur.WeierstrassDividedZeroEqualityOneZeroTerminalTensorCompatibility
public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroEqualityZeroTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityTerminalTensorDesc
public import FLT.Mazur.WeierstrassDividedZeroEqualityAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroEqualityAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroEqualityInteriorTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositiveAtlasFamily

/-!
# The equality depth-one original initial/terminal atlas intersection

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
  (D : SplitNodeDepth W π depth) (hs : 1 + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + 1 + 1) ≤ depth)
  (hp : 2 * (start + 1 + 1) = depth)
local notation "K" => ResidueField R
local notation "g" => adjacentRetainedOldGlobalTensorChart hπ data K 0 (by omega) 0 hs
local notation "gNext" => olderGlobalTensorChart hπ data K (0 + 1) (by omega) 0 hs
local notation "m" => globalTensorAtlasMap hπ data K (1 + 1) hs
local notation "i" => (Fin.mk 3 (by omega) : Fin (1 + 1 + 3))
local notation "iNext" => (Fin.mk 2 (by omega) : Fin (1 + 1 + 3))
local notation "V" => zeroSplitCycleZeroAtlasIso hπ data 1 hs
local notation "N" => olderSuccessiveTensorAtlasIso hπ data K 1 hs 0 hs

variable {Y : Scheme.{u}}
  (F : Fin (2 * 1 + 2) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ index, ProjectiveLine.zero (ResidueField R) ≫ F index =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) index))
local notation "d" => zeroEqualityPositiveCycleAtlasFamily
  hπ data D 1 hs hstart hk hp (by omega) F w

/-- The complete start-zero and positive neighbor intersection is compatible. -/
theorem zeroEqualityPositiveAtlasCompatible_one_zero_terminal :
    ZeroEqualityPositiveAtlasCompatible hπ data D 1 hs hstart hk hp (by omega) F w i iNext := by
  apply pullback_compatible_of_source_isos V N g gNext (m i) (m iNext) (d i) (d iNext)
    (finiteGlobalTensorModel_index_congr hπ data K hs (by omega) (by omega))
  · rw [zeroSplitCycleZeroAtlasIso_global]
    apply (comp_eqToHom_heq _ _).trans
    exact (olderGlobalTensorChart_retention_heq hπ data 0 (by omega)
      1 (0 + 1) (by omega) (by omega) (by omega)).trans
        (adjacentRetainedOldGlobalTensorChart_heq hπ data K 0 (by omega) 0 hs)
  · exact heq_of_eq (olderGlobalTensorChart_eq_index hπ data K 1 hs 0 hs)
  · rw [zeroEqualityPositiveCycleAtlasFamily_terminal_retained]
    have H := zeroEqualityCycleOneZeroTerminalTensorDesc_compatible
      hπ data D hs hstart hk hp 0 hs F w
    simpa only [zeroEqualityPositiveCycleZeroTensorDesc,
      zeroEqualityCycleTerminalTensorDesc, Category.assoc] using H

end FLT.Mazur.WeierstrassDividedDepth
