/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCycleAtlasFamily
import all FLT.Mazur.WeierstrassDividedZeroCyclePositiveIndexedMap
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasFamily
import all FLT.Mazur.WeierstrassDividedZeroCycleLocalMaps

/-!
# Original ordered nodes in the fixed cyclic atlas

The two node inclusions use the actual fixed atlas index. Their global maps
and descended restrictions retain the original ordered node morphisms.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hp : 2 * (start + s + 1) < depth) (j : Fin s)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j.val + 1 + 1) (by omega))
local notation "c" => residue R (Data.b6 e)
local notation "U" => olderIndexedNodeOpenCover hπ data D (j.val + 1) (by omega)
  (s - (j.val + 1)) (by omega) (by omega) (by omega)
local notation "transport" => eqToHom (globalTensorAtlasObject_index_congr hπ data
  (a := j.val + 2 + (s - (j.val + 1))) (by omega) hs (by omega)
  (Fin.succ (Fin.mk (s - (j.val + 1) + 1) (by omega)))
  (Fin.mk (s - j.val + 1) (by omega)) (by dsimp; omega))
local notation "targetTransport" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (by omega : j.val + 2 + (s - (j.val + 1)) ≤ n) hs (by omega))
local notation "G" => globalTensorAtlasMap hπ data K (s + 1) hs
  (Fin.mk (s - j.val + 1) (by omega))

/-- The first original node inside the fixed positive retained chart. -/
def zeroSplitCyclePositiveAtlasFirstNode : Spec (.of (MiddleNodeOpen c)) ⟶
    globalTensorAtlasObject hπ data K (s + 1) hs ⟨s - j.val + 1, by omega⟩ :=
  (U).f (0 : Fin 2) ≫ transport

/-- The opposite ordered node inside the same fixed retained chart. -/
def zeroSplitCyclePositiveAtlasSecondNode : Spec (.of (MiddleNodeOpen c)) ⟶
    globalTensorAtlasObject hπ data K (s + 1) hs ⟨s - j.val + 1, by omega⟩ :=
  (U).f (1 : Fin 2) ≫ transport

/-- The fixed first node retains its original global inclusion. -/
@[reassoc] theorem zeroSplitCyclePositiveAtlasFirstNode_global :
    zeroSplitCyclePositiveAtlasFirstNode hπ data D s hs hstart hp j ≫ G =
      olderGlobalResidueFirstNode hπ data D (j.val + 1) (by omega)
        (s - (j.val + 1)) (by omega) (by omega) (by omega) ≫ targetTransport := by
  rw [zeroSplitCyclePositiveAtlasFirstNode, Category.assoc,
    globalTensorAtlasMap_index_transport hπ data (by omega) hs (by omega)
      _ _ (by dsimp; omega)]
  exact olderIndexedNodeMap_first_global_assoc hπ data D (j.val + 1) (by omega)
    (s - (j.val + 1)) (by omega) (by omega) (by omega) targetTransport

/-- The fixed second node retains the opposite original global inclusion. -/
@[reassoc] theorem zeroSplitCyclePositiveAtlasSecondNode_global :
    zeroSplitCyclePositiveAtlasSecondNode hπ data D s hs hstart hp j ≫ G =
      olderGlobalResidueSecondNode hπ data D (j.val + 1) (by omega)
        (s - (j.val + 1)) (by omega) (by omega) (by omega) ≫ targetTransport := by
  rw [zeroSplitCyclePositiveAtlasSecondNode, Category.assoc,
    globalTensorAtlasMap_index_transport hπ data (by omega) hs (by omega)
      _ _ (by dsimp; omega)]
  exact olderIndexedNodeMap_second_global_assoc hπ data D (j.val + 1) (by omega)
    (s - (j.val + 1)) (by omega) (by omega) (by omega) targetTransport

variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "d" => zeroSplitCycleAtlasFamily hπ data D s hs hstart hp F w
  (Fin.mk (s - j.val + 1) (by omega))

/-- The fixed atlas family restricts to the first complete original node descent. -/
@[reassoc] theorem zeroSplitCyclePositiveAtlasFirstNode_desc :
    zeroSplitCyclePositiveAtlasFirstNode hπ data D s hs hstart hp j ≫ d =
      zeroSplitCycleFirstLocalDesc data D s hs hstart hp j F w := by
  rw [zeroSplitCycleAtlasFamily_positive, zeroSplitCyclePositiveAtlasFirstNode,
    Category.assoc, zeroSplitCyclePositiveIndexedDesc_first]

/-- The fixed atlas family restricts to the opposite complete original node descent. -/
@[reassoc] theorem zeroSplitCyclePositiveAtlasSecondNode_desc :
    zeroSplitCyclePositiveAtlasSecondNode hπ data D s hs hstart hp j ≫ d =
      zeroSplitCycleSecondLocalDesc data D s hs hstart hp j F w := by
  rw [zeroSplitCycleAtlasFamily_positive, zeroSplitCyclePositiveAtlasSecondNode,
    Category.assoc, zeroSplitCyclePositiveIndexedDesc_second]

end FLT.Mazur.WeierstrassDividedDepth
