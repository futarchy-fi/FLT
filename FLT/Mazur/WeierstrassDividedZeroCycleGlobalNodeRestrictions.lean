/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCycleGlobalDesc
import all FLT.Mazur.WeierstrassDividedZeroCycleGlobalDesc
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasFamily
import all FLT.Mazur.WeierstrassDividedZeroCyclePositiveIndexedMap
import all FLT.Mazur.WeierstrassDividedZeroCycleZeroIndexedMap

/-!
# Global cyclic descent on the original ordered retained nodes

The original atlas restrictions recover both full local descents after the
explicit source and target index transports.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hp : 2 * (start + s + 1) < depth)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "K" => ResidueField R
local notation "d" => zeroSplitCycleGlobalDesc hπ data D s hs hstart hp F w

section Positive
variable (j : Fin s)
local notation "t" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (by omega : j.val + 2 + (s - (j.val + 1)) ≤ n) hs (by omega))
local notation "v" => eqToHom (globalTensorAtlasObject_index_congr hπ data
  (a := j.val + 2 + (s - (j.val + 1))) (by omega) hs (by omega)
  (Fin.succ (Fin.mk ((s - (j.val + 1)) + 1) (by omega)))
  (Fin.mk (s - j.val + 1) (by omega)) (by dsimp; omega))
local notation "f" => olderIndexedNodeMap hπ data D (j.val + 1) (by omega) (s - (j.val + 1))
  (by omega) (by omega) (by omega)

/-- Global descent recovers the entire first ordered positive node map. -/
@[reassoc] theorem zeroSplitCycleGlobalDesc_positive_first :
    olderGlobalResidueFirstNode hπ data D (j.val + 1) (by omega) (s - (j.val + 1))
        (by omega) (by omega) (by omega) ≫ t ≫ d =
      zeroSplitCycleFirstLocalDesc data D s hs hstart hp j F w := by
  have H := congrArg (fun q => f 0 ≫ v ≫ q)
    (zeroSplitCycleGlobalDesc_atlas hπ data D s hs hstart hp F w
      ⟨s - j.val + 1, by omega⟩)
  rw [globalTensorAtlasMap_index_transport_assoc hπ data (by omega) hs (by omega)
    _ _ (by dsimp; omega),
    olderIndexedNodeMap_first_global_assoc,
    zeroSplitCycleAtlasFamily_positive] at H
  exact H.trans (zeroSplitCyclePositiveIndexedDesc_first
    hπ data D s hs hstart hp j F w)

/-- Global descent recovers the entire second ordered positive node map. -/
@[reassoc] theorem zeroSplitCycleGlobalDesc_positive_second :
    olderGlobalResidueSecondNode hπ data D (j.val + 1) (by omega) (s - (j.val + 1))
        (by omega) (by omega) (by omega) ≫ t ≫ d =
      zeroSplitCycleSecondLocalDesc data D s hs hstart hp j F w := by
  have H := congrArg (fun q => f 1 ≫ v ≫ q)
    (zeroSplitCycleGlobalDesc_atlas hπ data D s hs hstart hp F w
      ⟨s - j.val + 1, by omega⟩)
  rw [globalTensorAtlasMap_index_transport_assoc hπ data (by omega) hs (by omega)
    _ _ (by dsimp; omega),
    olderIndexedNodeMap_second_global_assoc,
    zeroSplitCycleAtlasFamily_positive] at H
  exact H.trans (zeroSplitCyclePositiveIndexedDesc_second
    hπ data D s hs hstart hp j F w)

end Positive
section Zero
local notation "t" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (by omega : 0 + 1 + s ≤ n) hs (by omega))
local notation "v" => eqToHom (globalTensorAtlasObject_index_congr hπ data
  (a := 0 + 1 + s) (by omega) hs (by omega)
  (Fin.succ (Fin.mk (s + 1) (by omega)))
  (Fin.mk (s + 2) (by omega)) (by rfl))
local notation "f" => olderZeroIndexedNodeMap hπ data D 0 (by omega) s
  (by omega) (by omega) (by omega)

/-- Global descent recovers the entire first ordered attachment node map. -/
@[reassoc] theorem zeroSplitCycleGlobalDesc_attachment_first :
    olderGlobalZeroFirstNode hπ data D 0 (by omega) s
        (by omega) (by omega) (by omega) ≫ t ≫ d =
      zeroSplitCycleFirstAttachmentDesc data D s hs hp F w := by
  have H := congrArg (fun q => f 0 ≫ v ≫ q)
    (zeroSplitCycleGlobalDesc_atlas hπ data D s hs hstart hp F w
      ⟨s + 2, by omega⟩)
  rw [globalTensorAtlasMap_index_transport_assoc hπ data (by omega) hs (by omega)
    _ _ (by rfl),
    olderZeroIndexedNodeMap_first_global_assoc,
    zeroSplitCycleAtlasFamily_zero] at H
  exact H.trans (zeroSplitCycleZeroIndexedDesc_first
    hπ data D s hs hstart hp F w)

/-- Global descent recovers the entire second ordered attachment node map. -/
@[reassoc] theorem zeroSplitCycleGlobalDesc_attachment_second :
    olderGlobalZeroSecondNode hπ data D 0 (by omega) s
        (by omega) (by omega) (by omega) ≫ t ≫ d =
      zeroSplitCycleSecondAttachmentDesc data D s hs hp F w := by
  have H := congrArg (fun q => f 1 ≫ v ≫ q)
    (zeroSplitCycleGlobalDesc_atlas hπ data D s hs hstart hp F w
      ⟨s + 2, by omega⟩)
  rw [globalTensorAtlasMap_index_transport_assoc hπ data (by omega) hs (by omega)
    _ _ (by rfl),
    olderZeroIndexedNodeMap_second_global_assoc,
    zeroSplitCycleAtlasFamily_zero] at H
  exact H.trans (zeroSplitCycleZeroIndexedDesc_second
    hπ data D s hs hstart hp F w)

end Zero

end FLT.Mazur.WeierstrassDividedDepth
