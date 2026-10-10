/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveAtlasBranches
import all FLT.Mazur.WeierstrassDividedZeroCyclePositiveAtlasNodes
import all FLT.Mazur.WeierstrassDividedZeroCyclePositiveIndexedMap
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasFamily
import all FLT.Mazur.WeierstrassDividedZeroCycleLocalMaps
import all FLT.Mazur.WeierstrassDividedTensorAtlasComparison
import all FLT.Mazur.WeierstrassDividedGlobalTensorAtlas

/-!
# The complete positive retained tensor chart at its fixed cyclic atlas index

Only numerical stage and index transports enter this isomorphism. Its two
original residue nodes become the already constructed fixed atlas nodes.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (j : Fin s)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j.val + 1 + 1) (by omega))
local notation "c" => residue R (Data.b6 e)
local notation "transport" => eqToHom (globalTensorAtlasObject_index_congr hπ data
  (a := j.val + 2 + (s - (j.val + 1))) (by omega) hs (by omega)
  (Fin.succ (Fin.mk (s - (j.val + 1) + 1) (by omega)))
  (Fin.mk (s - j.val + 1) (by omega)) (by dsimp; omega))
local notation "targetTransport" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (by omega : j.val + 2 + (s - (j.val + 1)) ≤ n) hs (by omega))
local notation "G" => globalTensorAtlasMap hπ data K (s + 1) hs
  (Fin.mk (s - j.val + 1) (by omega))

local notation "V" => olderSuccessiveTensorAtlasIso hπ data K (j.val + 1) (by omega)
  (s - (j.val + 1)) (by omega)
/-- The entire original tensor chart at the fixed positive cyclic atlas index. -/
def zeroSplitCyclePositiveAtlasIso :
    Spec (.of (ScalarExtension W (π ^ (start + (j.val + 1))) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e) K)) ≅
        globalTensorAtlasObject hπ data K (s + 1) hs ⟨s - j.val + 1, by omega⟩ :=
  (V).trans (asIso transport)

/-- The complete chart isomorphism preserves the original global tensor map. -/
@[reassoc] theorem zeroSplitCyclePositiveAtlasIso_global :
    (zeroSplitCyclePositiveAtlasIso hπ data s hs j).hom ≫ G =
      olderGlobalTensorChart hπ data K (j.val + 1) (by omega)
        (s - (j.val + 1)) (by omega) ≫ targetTransport := by
  simp only [zeroSplitCyclePositiveAtlasIso, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [globalTensorAtlasMap_index_transport hπ data
    (a := j.val + 2 + (s - (j.val + 1))) (by omega) hs (by omega)
    (Fin.succ (Fin.mk (s - (j.val + 1) + 1) (by omega)))
    (Fin.mk (s - j.val + 1) (by omega)) (by dsimp; omega),
    ← Category.assoc, olderGlobalTensorChart_eq_index]

variable {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hstart : start = 0) (hp : 2 * (start + s + 1) < depth)
local notation "N₁" => residueMiddleFirstNodeChart D (start + (j.val + 1)) (by omega)
  (by omega) (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "N₂" => residueMiddleSecondNodeChart D (start + (j.val + 1)) (by omega)
  (by omega) (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)

omit [IsBezout R] in
/-- The first node inclusion is unchanged by the fixed source transport. -/
@[reassoc] theorem zeroSplitCyclePositiveAtlasIso_firstNode :
    N₁ ≫ (zeroSplitCyclePositiveAtlasIso hπ data s hs j).hom =
      zeroSplitCyclePositiveAtlasFirstNode hπ data D s hs hstart hp j := by
  change _ ≫ (_ ≫ transport) = (_ ≫ _) ≫ transport
  exact (Category.assoc _ _ _).symm

omit [IsBezout R] in
/-- The second node inclusion retains its original tangent ordering. -/
@[reassoc] theorem zeroSplitCyclePositiveAtlasIso_secondNode :
    N₂ ≫ (zeroSplitCyclePositiveAtlasIso hπ data s hs j).hom =
      zeroSplitCyclePositiveAtlasSecondNode hπ data D s hs hstart hp j := by
  change _ ≫ (_ ≫ transport) = (_ ≫ _) ≫ transport
  exact (Category.assoc _ _ _).symm

variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))

/-- Pull the fixed family back to the complete original retained tensor chart. -/
def zeroSplitCyclePositiveTensorDesc :=
  (zeroSplitCyclePositiveAtlasIso hπ data s hs j).hom ≫
    zeroSplitCycleAtlasFamily hπ data D s hs hstart hp F w ⟨s - j.val + 1, by omega⟩

/-- Its first full node restriction is the constructed local cyclic descent. -/
@[reassoc] theorem zeroSplitCyclePositiveTensorDesc_first :
    N₁ ≫
      zeroSplitCyclePositiveTensorDesc hπ data s hs j D hstart hp F w =
      zeroSplitCycleFirstLocalDesc data D s hs hstart hp j F w := by
  rw [zeroSplitCyclePositiveTensorDesc, zeroSplitCyclePositiveAtlasIso_firstNode_assoc,
    zeroSplitCyclePositiveAtlasFirstNode_desc]

/-- Its second full node restriction keeps the original opposite descent. -/
@[reassoc] theorem zeroSplitCyclePositiveTensorDesc_second :
    N₂ ≫
      zeroSplitCyclePositiveTensorDesc hπ data s hs j D hstart hp F w =
      zeroSplitCycleSecondLocalDesc data D s hs hstart hp j F w := by
  rw [zeroSplitCyclePositiveTensorDesc, zeroSplitCyclePositiveAtlasIso_secondNode_assoc,
    zeroSplitCyclePositiveAtlasSecondNode_desc]

end FLT.Mazur.WeierstrassDividedDepth
