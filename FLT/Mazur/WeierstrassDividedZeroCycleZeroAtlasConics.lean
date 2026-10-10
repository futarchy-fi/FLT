/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCycleAtlasFamily
public import FLT.Mazur.WeierstrassDividedZeroCycleAttachmentBranches
import all FLT.Mazur.WeierstrassDividedZeroCycleZeroIndexedMap
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasFamily
import all FLT.Mazur.WeierstrassDividedZeroCycleAttachmentMaps

/-!
# Complete conic branches in the oldest fixed cyclic atlas chart

Both original conic parameters map to the actual oldest chart, retaining
their global cyclic components and the prescribed descended restrictions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk 1 (by omega))
local notation "c" => residue R (Data.b6 e)
local notation "α" => residue R W.a₁
local notation "ha" => D.a₁_unit.map (residue R)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + 1) (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "E" => conicZeroAffineIso c hc
local notation "f" => olderZeroIndexedNodeMap hπ data D 0 (by omega) s (by omega)
  (by omega) (by omega)
local notation "transport" => eqToHom (globalTensorAtlasObject_index_congr hπ data
  (a := 0 + 1 + s) (by omega) hs (by omega)
  (Fin.succ (Fin.mk (s + 1) (by omega))) (Fin.mk (s + 2) (by omega)) (by rfl))
local notation "G" => globalTensorAtlasMap hπ data K (s + 1) hs
  (Fin.mk (s + 2) (by omega))
local notation "Z" => zeroSplitCycleComponent hπ data D s hs hstart (by omega) hp

/-- The complete first conic branch in the actual oldest retained atlas object. -/
def zeroSplitCycleZeroAtlasFirstConic : ProjectiveLine.chart K ⟶
    globalTensorAtlasObject hπ data K (s + 1) hs ⟨s + 2, by omega⟩ :=
  (E).hom ≫ (fullNodeConicParameterIso α c ha).hom ≫
    fullNodeFirstBranch α c ha ≫ f 0 ≫ transport

/-- The oldest first conic map is the unchanged chart of its cyclic component. -/
@[reassoc] theorem zeroSplitCycleZeroAtlasFirstConic_global :
    zeroSplitCycleZeroAtlasFirstConic hπ data D s hs hstart hp ≫ G =
      ProjectiveLine.right K ≫ (Z 1).left := by
  simp only [zeroSplitCycleZeroAtlasFirstConic, Category.assoc]
  rw [globalTensorAtlasMap_index_transport hπ data (by omega) hs (by omega)
    _ _ (by rfl), olderZeroIndexedNodeMap_first_global_assoc]
  exact (zeroSplitCycleComponent_first_attachment_conic
    hπ data D s hs hstart (by omega) hp).symm

/-- The complete second conic branch in the actual oldest retained atlas object. -/
def zeroSplitCycleZeroAtlasSecondConic : ProjectiveLine.chart K ⟶
    globalTensorAtlasObject hπ data K (s + 1) hs ⟨s + 2, by omega⟩ :=
  (E).hom ≫ (fullNodeConicParameterIso (-α) c (ha).neg).hom ≫
    fullNodeFirstBranch (-α) c (ha).neg ≫ f 1 ≫ transport

/-- The oldest second conic map is the unchanged chart of its cyclic component. -/
@[reassoc] theorem zeroSplitCycleZeroAtlasSecondConic_global :
    zeroSplitCycleZeroAtlasSecondConic hπ data D s hs hstart hp ≫ G =
      ProjectiveLine.left K ≫ (Z ⟨2 * s + 2, by omega⟩).left := by
  simp only [zeroSplitCycleZeroAtlasSecondConic, Category.assoc]
  rw [globalTensorAtlasMap_index_transport hπ data (by omega) hs (by omega)
    _ _ (by rfl), olderZeroIndexedNodeMap_second_global_assoc]
  exact (zeroSplitCycleComponent_second_attachment_conic
    hπ data D s hs hstart (by omega) hp).symm

variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "d" => zeroSplitCycleAtlasFamily hπ data D s hs hstart hp F w
  (Fin.mk (s + 2) (by omega))

/-- The oldest first conic restriction recovers the original cyclic family map. -/
@[reassoc] theorem zeroSplitCycleZeroAtlasFirstConic_desc :
    zeroSplitCycleZeroAtlasFirstConic hπ data D s hs hstart hp ≫ d =
      ProjectiveLine.right K ≫ F 1 := by
  rw [zeroSplitCycleAtlasFamily_zero]
  simp only [zeroSplitCycleZeroAtlasFirstConic, Category.assoc,
    zeroSplitCycleZeroIndexedDesc_first]
  exact zeroSplitCycleFirstAttachmentDesc_conic data D s hs hp F w

/-- The oldest second conic restriction recovers the original cyclic family map. -/
@[reassoc] theorem zeroSplitCycleZeroAtlasSecondConic_desc :
    zeroSplitCycleZeroAtlasSecondConic hπ data D s hs hstart hp ≫ d =
      ProjectiveLine.left K ≫ F ⟨2 * s + 2, by omega⟩ := by
  rw [zeroSplitCycleAtlasFamily_zero]
  simp only [zeroSplitCycleZeroAtlasSecondConic, Category.assoc,
    zeroSplitCycleZeroIndexedDesc_second]
  exact zeroSplitCycleSecondAttachmentDesc_conic data D s hs hp F w

end FLT.Mazur.WeierstrassDividedDepth
