/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCycleZeroPositiveTensorCompatibility
import all FLT.Mazur.WeierstrassDividedZeroCycleZeroPositiveTensorCompatibility
public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroCycleZeroTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroCyclePositiveTensorCompatibility
public import FLT.Mazur.WeierstrassDividedZeroCycleAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroCyclePositiveTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasFamily

/-!
# Full start-zero neighbor compatibility at the fixed original atlas indices

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
  (hstart : start = 0) (hp : 2 * (start + s + 1) < depth) (hs0 : 0 < s)
local notation "K" => ResidueField R
local notation "firstJ" => (Fin.mk 0 hs0 : Fin s)
local notation "r" => s - 1
local notation "g" => adjacentRetainedOldGlobalTensorChart hπ data K 0 (by omega) r (by omega)
local notation "gNext" => olderGlobalTensorChart hπ data K (0 + 1) (by omega) r (by omega)
local notation "m" => globalTensorAtlasMap hπ data K (s + 1) hs
local notation "i" => (Fin.mk (s + 2) (by omega) : Fin (s + 1 + 3))
local notation "iNext" => (Fin.mk (s - Fin.val firstJ + 1) (by omega) : Fin (s + 1 + 3))
local notation "V" => zeroSplitCycleZeroAtlasIso hπ data s hs
local notation "N" => zeroSplitCyclePositiveAtlasIso hπ data s hs firstJ

variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ index, ProjectiveLine.zero (ResidueField R) ≫ F index =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) index))
local notation "d" => zeroSplitCycleAtlasFamily hπ data D s hs hstart hp F w

/-- The complete start-zero and positive neighbor intersection is compatible. -/
theorem zeroSplitCycleAtlasCompatible_zero_positive :
    ZeroSplitCycleAtlasCompatible hπ data D s hs hstart hp F w i iNext := by
  apply pullback_compatible_of_source_isos V N g gNext (m i) (m iNext) (d i) (d iNext)
    (finiteGlobalTensorModel_index_congr hπ data K hs (by omega) (by omega))
  · rw [zeroSplitCycleZeroAtlasIso_global]
    apply (comp_eqToHom_heq _ _).trans
    exact (olderGlobalTensorChart_retention_heq hπ data 0 (by omega)
      s (r + 1) (by omega) (by omega) (by omega)).trans
        (adjacentRetainedOldGlobalTensorChart_heq hπ data K 0 (by omega) r (by omega))
  · rw [zeroSplitCyclePositiveAtlasIso_global]
    exact comp_eqToHom_heq _ _
  · have H := zeroSplitCycleZeroPositiveTensorDesc_compatible
      hπ data D s hs hstart hp hs0 r (by omega) F w
    simpa only [zeroSplitCycleZeroTensorDesc, zeroSplitCyclePositiveTensorDesc,
      Category.assoc] using H

/-- In the increasing atlas order, the last retained pair is proved whenever s is positive. -/
theorem zeroSplitCycleAtlasCompatible_zero_neighbor :
    ZeroSplitCycleAtlasCompatible hπ data D s hs hstart hp F w ⟨s + 1, by omega⟩ i := by
  simpa only [Fin.val_mk, Nat.sub_zero] using
    zeroSplitCycleAtlasCompatible_symm hπ data D s hs hstart hp F w
      (zeroSplitCycleAtlasCompatible_zero_positive hπ data D s hs hstart hp hs0 F w)

end FLT.Mazur.WeierstrassDividedDepth
