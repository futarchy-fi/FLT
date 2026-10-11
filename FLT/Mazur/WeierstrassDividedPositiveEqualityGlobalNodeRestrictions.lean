/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityGlobalDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityGlobalDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasFamily
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorIndexedDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalIndexedDesc

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
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 4) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "K" => ResidueField R
local notation "d" => positiveEqualityCycleGlobalDesc hπ data D s hs hstart hk hp F w

section Positive
variable (j : Fin s)
local notation "t" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (by omega : j.val + 1 + (s - j.val) ≤ n) hs (by omega))
local notation "v" => eqToHom (globalTensorAtlasObject_index_congr hπ data
  (a := j.val + 1 + (s - j.val)) (by omega) hs (by omega)
  (Fin.succ (Fin.mk ((s - j.val) + 1) (by omega)))
  (Fin.mk (s - j.val + 2) (by omega)) (by rfl))
local notation "f" => olderIndexedNodeMap hπ data D j.val (by omega) (s - j.val)
  (by omega) (by omega) (by omega)

/-- Global descent recovers the entire first ordered positive node map. -/
@[reassoc] theorem positiveEqualityCycleGlobalDesc_positive_first :
    olderGlobalResidueFirstNode hπ data D j.val (by omega) (s - j.val)
        (by omega) (by omega) (by omega) ≫ t ≫ d =
      positiveEqualityCycleInteriorFirstLocalDesc data D s hs hk j F w := by
  have H := congrArg (fun q => f 0 ≫ v ≫ q)
    (positiveEqualityCycleGlobalDesc_atlas hπ data D s hs hstart hk hp F w
      ⟨s - j.val + 2, by omega⟩)
  rw [globalTensorAtlasMap_index_transport_assoc hπ data (by omega) hs (by omega)
    _ _ (by rfl),
    olderIndexedNodeMap_first_global_assoc,
    positiveEqualityCycleAtlasFamily_positive] at H
  exact H.trans (positiveEqualityCycleInteriorIndexedDesc_first
    hπ data D s hs hstart hk j F w)

/-- Global descent recovers the entire second ordered positive node map. -/
@[reassoc] theorem positiveEqualityCycleGlobalDesc_positive_second :
    olderGlobalResidueSecondNode hπ data D j.val (by omega) (s - j.val)
        (by omega) (by omega) (by omega) ≫ t ≫ d =
      positiveEqualityCycleInteriorSecondLocalDesc data D s hs hk j F w := by
  have H := congrArg (fun q => f 1 ≫ v ≫ q)
    (positiveEqualityCycleGlobalDesc_atlas hπ data D s hs hstart hk hp F w
      ⟨s - j.val + 2, by omega⟩)
  rw [globalTensorAtlasMap_index_transport_assoc hπ data (by omega) hs (by omega)
    _ _ (by rfl),
    olderIndexedNodeMap_second_global_assoc,
    positiveEqualityCycleAtlasFamily_positive] at H
  exact H.trans (positiveEqualityCycleInteriorIndexedDesc_second
    hπ data D s hs hstart hk j F w)

end Positive
section Terminal
local notation "f" => olderIndexedNodeMap hπ data D s hs 0 hs (by omega) hk

/-- The entire first terminal node retains its arbitrary-constant attachment descent. -/
@[reassoc] theorem positiveEqualityCycleGlobalDesc_terminal_first :
    olderGlobalResidueFirstNode hπ data D s hs 0 hs (by omega) hk ≫ d =
      positiveEqualityCycleTerminalFirstDesc data D s hs hk hp F w := by
  have H := congrArg (fun q => f 0 ≫ q)
    (positiveEqualityCycleGlobalDesc_atlas hπ data D s hs hstart hk hp F w
      ⟨2, by omega⟩)
  have Hnode : f 0 ≫ globalTensorAtlasMap hπ data K (s + 1) hs ⟨2, by omega⟩ =
      olderGlobalResidueFirstNode hπ data D s hs 0 hs (by omega) hk :=
    olderIndexedNodeMap_first_global hπ data D s hs 0 hs (by omega) hk
  rw [← Category.assoc, Hnode, positiveEqualityCycleAtlasFamily_terminal_retained] at H
  exact H.trans (positiveEqualityCycleTerminalIndexedDesc_first hπ data D s hs hstart hk hp F w)

/-- The entire opposite terminal node preserves its original negative conic parameter. -/
@[reassoc] theorem positiveEqualityCycleGlobalDesc_terminal_second :
    olderGlobalResidueSecondNode hπ data D s hs 0 hs (by omega) hk ≫ d =
      positiveEqualityCycleTerminalSecondDesc data D s hs hk hp F w := by
  have H := congrArg (fun q => f 1 ≫ q)
    (positiveEqualityCycleGlobalDesc_atlas hπ data D s hs hstart hk hp F w
      ⟨2, by omega⟩)
  have Hnode : f 1 ≫ globalTensorAtlasMap hπ data K (s + 1) hs ⟨2, by omega⟩ =
      olderGlobalResidueSecondNode hπ data D s hs 0 hs (by omega) hk :=
    olderIndexedNodeMap_second_global hπ data D s hs 0 hs (by omega) hk
  rw [← Category.assoc, Hnode, positiveEqualityCycleAtlasFamily_terminal_retained] at H
  exact H.trans (positiveEqualityCycleTerminalIndexedDesc_second hπ data D s hs hstart hk hp F w)

end Terminal

end FLT.Mazur.WeierstrassDividedDepth
