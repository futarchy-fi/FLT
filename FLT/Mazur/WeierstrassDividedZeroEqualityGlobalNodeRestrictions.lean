/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityPositiveAtlasDescent
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositiveAtlasDescent
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositiveAtlasFamily
import all FLT.Mazur.WeierstrassDividedZeroEqualityInteriorIndexedDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositiveInitialDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityTerminalIndexedDesc

/-!
# Global equality-cycle descent on the original ordered retained nodes

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
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth) (hpos : 0 < s)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 2) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "K" => ResidueField R
local notation "d" => zeroEqualityPositiveCycleGlobalDesc hπ data D s hs hstart hk hp hpos F w

section Positive
variable (j : Fin (s - 1))
local notation "t" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (by omega : j.val + 2 + (s - (j.val + 1)) ≤ n) hs (by omega))
local notation "v" => eqToHom (globalTensorAtlasObject_index_congr hπ data
  (a := j.val + 2 + (s - (j.val + 1))) (by omega) hs (by omega)
  (Fin.succ (Fin.mk ((s - (j.val + 1)) + 1) (by omega)))
  (Fin.mk (s - j.val + 1) (by omega)) (by dsimp; omega))
local notation "f" => olderIndexedNodeMap hπ data D (j.val + 1) (by omega) (s - (j.val + 1))
  (by omega) (by omega) (by omega)

/-- Global descent recovers the entire first ordered positive node map. -/
@[reassoc] theorem zeroEqualityPositiveCycleGlobalDesc_positive_first :
    olderGlobalResidueFirstNode hπ data D (j.val + 1) (by omega) (s - (j.val + 1))
        (by omega) (by omega) (by omega) ≫ t ≫ d =
      zeroEqualityCycleInteriorFirstLocalDesc data D s hs hstart hk j F w := by
  have H := congrArg (fun q => f 0 ≫ v ≫ q)
    (zeroEqualityPositiveCycleGlobalDesc_atlas hπ data D s hs hstart hk hp hpos F w
      ⟨s - j.val + 1, by omega⟩)
  rw [globalTensorAtlasMap_index_transport_assoc hπ data (by omega) hs (by omega)
    _ _ (by dsimp; omega),
    olderIndexedNodeMap_first_global_assoc,
    zeroEqualityPositiveCycleAtlasFamily_positive] at H
  exact H.trans (zeroEqualityCycleInteriorIndexedDesc_first
    hπ data D s hs hstart hk j F w)

/-- Global descent recovers the entire second ordered positive node map. -/
@[reassoc] theorem zeroEqualityPositiveCycleGlobalDesc_positive_second :
    olderGlobalResidueSecondNode hπ data D (j.val + 1) (by omega) (s - (j.val + 1))
        (by omega) (by omega) (by omega) ≫ t ≫ d =
      zeroEqualityCycleInteriorSecondLocalDesc data D s hs hstart hk j F w := by
  have H := congrArg (fun q => f 1 ≫ v ≫ q)
    (zeroEqualityPositiveCycleGlobalDesc_atlas hπ data D s hs hstart hk hp hpos F w
      ⟨s - j.val + 1, by omega⟩)
  rw [globalTensorAtlasMap_index_transport_assoc hπ data (by omega) hs (by omega)
    _ _ (by dsimp; omega),
    olderIndexedNodeMap_second_global_assoc,
    zeroEqualityPositiveCycleAtlasFamily_positive] at H
  exact H.trans (zeroEqualityCycleInteriorIndexedDesc_second
    hπ data D s hs hstart hk j F w)

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
@[reassoc] theorem zeroEqualityPositiveCycleGlobalDesc_attachment_first :
    olderGlobalZeroFirstNode hπ data D 0 (by omega) s
        (by omega) (by omega) (by omega) ≫ t ≫ d =
      zeroEqualityPositiveCycleFirstAttachmentDesc data D s hs hk hpos F w := by
  have H := congrArg (fun q => f 0 ≫ v ≫ q)
    (zeroEqualityPositiveCycleGlobalDesc_atlas hπ data D s hs hstart hk hp hpos F w
      ⟨s + 2, by omega⟩)
  rw [globalTensorAtlasMap_index_transport_assoc hπ data (by omega) hs (by omega)
    _ _ (by rfl),
    olderZeroIndexedNodeMap_first_global_assoc,
    zeroEqualityPositiveCycleAtlasFamily_zero] at H
  exact H.trans (zeroEqualityPositiveCycleZeroIndexedDesc_first
    hπ data D s hs hstart hk hpos F w)

/-- Global descent recovers the entire second ordered attachment node map. -/
@[reassoc] theorem zeroEqualityPositiveCycleGlobalDesc_attachment_second :
    olderGlobalZeroSecondNode hπ data D 0 (by omega) s
        (by omega) (by omega) (by omega) ≫ t ≫ d =
      zeroEqualityPositiveCycleSecondAttachmentDesc data D s hs hk hpos F w := by
  have H := congrArg (fun q => f 1 ≫ v ≫ q)
    (zeroEqualityPositiveCycleGlobalDesc_atlas hπ data D s hs hstart hk hp hpos F w
      ⟨s + 2, by omega⟩)
  rw [globalTensorAtlasMap_index_transport_assoc hπ data (by omega) hs (by omega)
    _ _ (by rfl),
    olderZeroIndexedNodeMap_second_global_assoc,
    zeroEqualityPositiveCycleAtlasFamily_zero] at H
  exact H.trans (zeroEqualityPositiveCycleZeroIndexedDesc_second
    hπ data D s hs hstart hk hpos F w)

end Zero

section Terminal
local notation "f" => olderIndexedNodeMap hπ data D s hs 0 hs (by omega) hk

/-- The entire first terminal node retains its arbitrary-constant attachment descent. -/
@[reassoc] theorem zeroEqualityPositiveCycleGlobalDesc_terminal_first :
    olderGlobalResidueFirstNode hπ data D s hs 0 hs (by omega) hk ≫ d =
      zeroEqualityCycleTerminalFirstDesc data D s hs hk hp F w := by
  have H := congrArg (fun q => f 0 ≫ q)
    (zeroEqualityPositiveCycleGlobalDesc_atlas hπ data D s hs hstart hk hp hpos F w
      ⟨2, by omega⟩)
  have Hnode : f 0 ≫ globalTensorAtlasMap hπ data K (s + 1) hs ⟨2, by omega⟩ =
      olderGlobalResidueFirstNode hπ data D s hs 0 hs (by omega) hk :=
    olderIndexedNodeMap_first_global hπ data D s hs 0 hs (by omega) hk
  rw [← Category.assoc, Hnode, zeroEqualityPositiveCycleAtlasFamily_terminal_retained] at H
  exact H.trans (zeroEqualityCycleTerminalIndexedDesc_first hπ data D s hs hk hp hpos F w)

/-- The entire opposite terminal node preserves its original negative conic parameter. -/
@[reassoc] theorem zeroEqualityPositiveCycleGlobalDesc_terminal_second :
    olderGlobalResidueSecondNode hπ data D s hs 0 hs (by omega) hk ≫ d =
      zeroEqualityCycleTerminalSecondDesc data D s hs hk hp F w hpos := by
  have H := congrArg (fun q => f 1 ≫ q)
    (zeroEqualityPositiveCycleGlobalDesc_atlas hπ data D s hs hstart hk hp hpos F w
      ⟨2, by omega⟩)
  have Hnode : f 1 ≫ globalTensorAtlasMap hπ data K (s + 1) hs ⟨2, by omega⟩ =
      olderGlobalResidueSecondNode hπ data D s hs 0 hs (by omega) hk :=
    olderIndexedNodeMap_second_global hπ data D s hs 0 hs (by omega) hk
  rw [← Category.assoc, Hnode, zeroEqualityPositiveCycleAtlasFamily_terminal_retained] at H
  exact H.trans (zeroEqualityCycleTerminalIndexedDesc_second hπ data D s hs hk hp hpos F w)

end Terminal

end FLT.Mazur.WeierstrassDividedDepth
