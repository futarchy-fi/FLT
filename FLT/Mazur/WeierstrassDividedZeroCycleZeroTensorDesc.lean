/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCycleZeroAtlasConics
import all FLT.Mazur.WeierstrassDividedZeroCycleZeroAtlasConics
import all FLT.Mazur.WeierstrassDividedZeroCycleZeroIndexedMap
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasFamily
import all FLT.Mazur.WeierstrassDividedOlderZeroIndexedNodeCover
import all FLT.Mazur.WeierstrassDividedOlderGlobalZeroSuccessive
import all FLT.Mazur.WeierstrassDividedTensorAtlasComparison
import all FLT.Mazur.WeierstrassDividedGlobalTensorAtlas

/-!
# The complete start-zero tensor chart at its fixed cyclic atlas index

The source comparison preserves the entire oldest tensor chart and both full
localized node inclusions. The fixed atlas descent has its original conic maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (s : ℕ) (hs : s + 1 ≤ n)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (1) (by omega))
local notation "c" => residue R (Data.b6 e)
local notation "transport" => eqToHom (globalTensorAtlasObject_index_congr hπ data
  (a := 0 + 1 + s) (by omega) hs (by omega)
  (Fin.succ (Fin.mk (s + 1) (by omega)))
  (Fin.mk (s + 2) (by omega)) (by rfl))
local notation "targetTransport" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (by omega : 0 + 1 + s ≤ n) hs (by omega))
local notation "G" => globalTensorAtlasMap hπ data K (s + 1) hs
  (Fin.mk (s + 2) (by omega))

local notation "V" => olderSuccessiveTensorAtlasIso hπ data K 0 (by omega)
  s (by omega)
/-- The entire original tensor chart at the fixed start-zero cyclic atlas index. -/
def zeroSplitCycleZeroAtlasIso :
    Spec (.of (ScalarExtension W (π ^ (start + 0)) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e) K)) ≅
        globalTensorAtlasObject hπ data K (s + 1) hs ⟨s + 2, by omega⟩ :=
  (V).trans (asIso transport)

/-- The complete chart isomorphism preserves the original global tensor map. -/
@[reassoc] theorem zeroSplitCycleZeroAtlasIso_global :
    (zeroSplitCycleZeroAtlasIso hπ data s hs).hom ≫ G =
      olderGlobalTensorChart hπ data K 0 (by omega)
        s (by omega) ≫ targetTransport := by
  simp only [zeroSplitCycleZeroAtlasIso, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [globalTensorAtlasMap_index_transport hπ data
    (a := 0 + 1 + s) (by omega) hs (by omega)
    (Fin.succ (Fin.mk (s + 1) (by omega)))
    (Fin.mk (s + 2) (by omega)) (by rfl),
    ← Category.assoc, olderGlobalTensorChart_eq_index]

variable {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hstart : start = 0) (hp : 2 * (start + s + 1) < depth)
local notation "a" => residue R W.a₁
local notation "ha" => D.a₁_unit.map (residue R)
local notation "V₀" => zeroResidueFiberIso D (start + 0) (by omega) (by omega)
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "f" => olderZeroIndexedNodeMap hπ data D 0 (by omega) s (by omega)
  (by omega) (by omega)

omit [IsBezout R] in
/-- The complete normalized first node agrees with its original indexed inclusion. -/
@[reassoc] theorem zeroSplitCycleZeroAtlasIso_firstNode :
    fullFirstNodeChart a c ha ≫ Iso.hom V₀ ≫
      (zeroSplitCycleZeroAtlasIso hπ data s hs).hom = f 0 ≫ transport := by
  simp only [zeroSplitCycleZeroAtlasIso, olderZeroIndexedNodeMap,
    olderGlobalZeroAtlasIso, Iso.trans_hom, asIso_hom, Fin.cases_zero, Category.assoc]

omit [IsBezout R] in
/-- The complete opposite node retains its full localized tangent parameter. -/
@[reassoc] theorem zeroSplitCycleZeroAtlasIso_secondNode :
    fullSecondNodeChart a c ha ≫ Iso.hom V₀ ≫
      (zeroSplitCycleZeroAtlasIso hπ data s hs).hom = f 1 ≫ transport := by
  change fullSecondNodeChart a c ha ≫ (Iso.hom V₀ ≫ (Iso.hom V ≫ transport)) =
    (fullSecondNodeChart a c ha ≫ (Iso.hom V₀ ≫ Iso.hom V)) ≫ transport
  simp only [Category.assoc]

variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))

/-- The fixed oldest atlas descent on its complete original tensor source. -/
def zeroSplitCycleZeroTensorDesc :=
  (zeroSplitCycleZeroAtlasIso hπ data s hs).hom ≫
    zeroSplitCycleAtlasFamily hπ data D s hs hstart hp F w ⟨s + 2, by omega⟩

/-- Its first node restriction recovers the full attachment descent. -/
@[reassoc] theorem zeroSplitCycleZeroTensorDesc_first :
    fullFirstNodeChart a c ha ≫ Iso.hom V₀ ≫
      zeroSplitCycleZeroTensorDesc hπ data s hs D hstart hp F w =
        zeroSplitCycleFirstAttachmentDesc data D s hs hp F w := by
  rw [zeroSplitCycleZeroTensorDesc, zeroSplitCycleZeroAtlasIso_firstNode_assoc
    hπ data s hs D hstart hp,
    zeroSplitCycleAtlasFamily_zero, zeroSplitCycleZeroIndexedDesc_first]

/-- Its second node restriction recovers the opposite full attachment descent. -/
@[reassoc] theorem zeroSplitCycleZeroTensorDesc_second :
    fullSecondNodeChart a c ha ≫ Iso.hom V₀ ≫
      zeroSplitCycleZeroTensorDesc hπ data s hs D hstart hp F w =
        zeroSplitCycleSecondAttachmentDesc data D s hs hp F w := by
  rw [zeroSplitCycleZeroTensorDesc, zeroSplitCycleZeroAtlasIso_secondNode_assoc
    hπ data s hs D hstart hp,
    zeroSplitCycleAtlasFamily_zero, zeroSplitCycleZeroIndexedDesc_second]

end FLT.Mazur.WeierstrassDividedDepth
