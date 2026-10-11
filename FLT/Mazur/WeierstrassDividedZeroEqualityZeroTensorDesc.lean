/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCycleZeroTensorDesc
public import FLT.Mazur.WeierstrassDividedZeroEqualityPositiveAtlasFamily
import all FLT.Mazur.WeierstrassDividedZeroCycleZeroTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositiveInitialDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositiveAtlasFamily
import all FLT.Mazur.WeierstrassDividedOlderZeroIndexedNodeCover
import all FLT.Mazur.WeierstrassDividedOlderGlobalZeroSuccessive
import all FLT.Mazur.WeierstrassDividedTensorAtlasComparison
import all FLT.Mazur.WeierstrassDividedGlobalTensorAtlas

/-!
# The complete start-zero tensor chart of the equality cycle

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
variable {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth) (hpos : 0 < s)
local notation "a" => residue R W.a₁
local notation "ha" => D.a₁_unit.map (residue R)
local notation "V₀" => zeroResidueFiberIso D (start + 0) (by omega) (by omega)
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "f" => olderZeroIndexedNodeMap hπ data D 0 (by omega) s (by omega)
  (by omega) (by omega)

variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 2) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))

/-- The fixed oldest atlas descent on its complete original tensor source. -/
def zeroEqualityPositiveCycleZeroTensorDesc :
    Spec (.of (ScalarExtension W (π ^ (start + 0)) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e) K)) ⟶ Y :=
  (zeroSplitCycleZeroAtlasIso hπ data s hs).hom ≫
    zeroEqualityPositiveCycleAtlasFamily hπ data D s hs hstart hk hp hpos F w ⟨s + 2, by omega⟩

/-- Its first node restriction recovers the full attachment descent. -/
@[reassoc] theorem zeroEqualityPositiveCycleZeroTensorDesc_first :
    fullFirstNodeChart a c ha ≫ Iso.hom V₀ ≫
      zeroEqualityPositiveCycleZeroTensorDesc hπ data s hs D hstart hk hp hpos F w =
        zeroEqualityPositiveCycleFirstAttachmentDesc data D s hs hk hpos F w := by
  rw [zeroEqualityPositiveCycleZeroTensorDesc, zeroEqualityPositiveCycleAtlasFamily_zero]
  have H := zeroEqualityPositiveCycleZeroIndexedDesc_first
    hπ data D s hs hstart hk hpos F w
  simpa only [zeroSplitCycleZeroAtlasIso, olderZeroIndexedNodeMap,
    olderGlobalZeroAtlasIso, Iso.trans_hom, asIso_hom, Fin.cases_zero, Category.assoc] using H

/-- Its second node restriction recovers the opposite full attachment descent. -/
@[reassoc] theorem zeroEqualityPositiveCycleZeroTensorDesc_second :
    fullSecondNodeChart a c ha ≫ Iso.hom V₀ ≫
      zeroEqualityPositiveCycleZeroTensorDesc hπ data s hs D hstart hk hp hpos F w =
        zeroEqualityPositiveCycleSecondAttachmentDesc data D s hs hk hpos F w := by
  rw [zeroEqualityPositiveCycleZeroTensorDesc, zeroEqualityPositiveCycleAtlasFamily_zero]
  have H := zeroEqualityPositiveCycleZeroIndexedDesc_second
    hπ data D s hs hstart hk hpos F w
  change (fullSecondNodeChart a c ha ≫ (Iso.hom V₀ ≫
    (olderSuccessiveTensorAtlasIso hπ data K 0 (by omega) s (by omega)).hom)) ≫ _ ≫ _ = _ at H
  simpa only [zeroSplitCycleZeroAtlasIso, Iso.trans_hom, asIso_hom, Category.assoc] using H

end FLT.Mazur.WeierstrassDividedDepth
