/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitGlobalDesc
import all FLT.Mazur.WeierstrassDividedPositiveSplitGlobalDesc
import all FLT.Mazur.WeierstrassDividedPositiveSplitAtlasFamily
import all FLT.Mazur.WeierstrassDividedPositiveSplitRetainedIndexedDesc

/-!
# Global strict-cycle descent on the original ordered retained nodes

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
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 5) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "K" => ResidueField R
local notation "d" => positiveSplitCycleGlobalDesc hπ data D s hs hstart hk hp F w

section Positive
variable (j : Fin (s + 1))
local notation "t" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (by omega : j.val + 1 + (s - j.val) ≤ n) hs (by omega))
local notation "v" => eqToHom (globalTensorAtlasObject_index_congr hπ data
  (a := j.val + 1 + (s - j.val)) (by omega) hs (by omega)
  (Fin.succ (Fin.mk ((s - j.val) + 1) (by omega)))
  (Fin.mk (s - j.val + 2) (by omega)) (by rfl))
local notation "f" => olderIndexedNodeMap hπ data D j.val (by omega) (s - j.val)
  (by omega) (by omega) (by omega)

/-- Global descent recovers the entire first ordered positive node map. -/
@[reassoc] theorem positiveSplitCycleGlobalDesc_positive_first :
    olderGlobalResidueFirstNode hπ data D j.val (by omega) (s - j.val)
        (by omega) (by omega) (by omega) ≫ t ≫ d =
      positiveSplitCycleFirstLocalDesc data D s hs hp j F w := by
  have H := congrArg (fun q => f 0 ≫ v ≫ q)
    (positiveSplitCycleGlobalDesc_atlas hπ data D s hs hstart hk hp F w
      ⟨s - j.val + 2, by omega⟩)
  rw [globalTensorAtlasMap_index_transport_assoc hπ data (by omega) hs (by omega)
    _ _ (by rfl),
    olderIndexedNodeMap_first_global_assoc,
    positiveSplitCycleAtlasFamily_positive] at H
  exact H.trans (positiveSplitCycleRetainedIndexedDesc_first
    hπ data D s hs hstart hp j F w)

/-- Global descent recovers the entire second ordered positive node map. -/
@[reassoc] theorem positiveSplitCycleGlobalDesc_positive_second :
    olderGlobalResidueSecondNode hπ data D j.val (by omega) (s - j.val)
        (by omega) (by omega) (by omega) ≫ t ≫ d =
      positiveSplitCycleSecondLocalDesc data D s hs hp j F w := by
  have H := congrArg (fun q => f 1 ≫ v ≫ q)
    (positiveSplitCycleGlobalDesc_atlas hπ data D s hs hstart hk hp F w
      ⟨s - j.val + 2, by omega⟩)
  rw [globalTensorAtlasMap_index_transport_assoc hπ data (by omega) hs (by omega)
    _ _ (by rfl),
    olderIndexedNodeMap_second_global_assoc,
    positiveSplitCycleAtlasFamily_positive] at H
  exact H.trans (positiveSplitCycleRetainedIndexedDesc_second
    hπ data D s hs hstart hp j F w)

end Positive

end FLT.Mazur.WeierstrassDividedDepth
