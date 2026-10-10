/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleNodePushout
public import FLT.Mazur.WeierstrassDividedOlderIndexedNodeCover
public import FLT.Mazur.WeierstrassDividedOlderGlobalSections

/-!
# Full split-node refinements of the retained positive-depth charts

Strict depth makes the actual retained conic constant vanish. The original
ordered atlas cover therefore has complete split-node charts, preserving both
original global node sections and the entire images of the original opens.
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
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
  (hp : 2 * (start + j + 1) < depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => residue R (Data.b6 d)
local notation "Obj" => globalTensorAtlasObject hπ data K (j + 1 + r) hr
  (Fin.succ (Fin.mk (r + 1) (by omega)))
local notation "G" => globalTensorAtlasMap hπ data K (j + 1 + r) hr
  (Fin.succ (Fin.mk (r + 1) (by omega)))

omit [IsBezout R] in
include D hp in
/-- The actual retained conic coefficient vanishes at every strict divided depth. -/
theorem retainedNode_constant_zero : c = 0 := by
  apply (residue_eq_zero_iff _).mpr
  exact WeierstrassDilatation.divided_constant_mem D (start + (j + 1))
    (by omega) (Data.b6 d) (Data.factor6 d)

/-- The complete original ordered attachment source is the standard split-node scheme. -/
def retainedSplitNodeIso : PolygonNodeBranches.node K ≅ Spec (.of (MiddleNodeOpen c)) :=
  middleNodeIsoOfZero c (retainedNode_constant_zero data D j hj hp)

/-- Both full split-node charts map to the actual retained indexed atlas object. -/
def olderIndexedSplitNodeMap (i : Fin 2) : PolygonNodeBranches.node K ⟶ Obj :=
  (retainedSplitNodeIso data D j hj hp).hom ≫
    olderIndexedNodeMap hπ data D j hj r hr hk0 hk i

instance olderIndexedSplitNodeMap_isOpenImmersion (i : Fin 2) :
    IsOpenImmersion (olderIndexedSplitNodeMap hπ data D j hj r hr hk0 hk hp i) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

omit [IsBezout R] in
/-- Normalization retains the full original image of each ordered attachment chart. -/
theorem olderIndexedSplitNodeMap_range (i : Fin 2) :
    Set.range (olderIndexedSplitNodeMap hπ data D j hj r hr hk0 hk hp i) =
      Set.range (olderIndexedNodeMap hπ data D j hj r hr hk0 hk i) :=
  (retainedSplitNodeIso data D j hj hp).hom.homeomorph.surjective.range_comp _

omit [IsBezout R] in
/-- The complete split nodes cover every point of the original retained chart. -/
theorem olderIndexedSplitNodeMap_cover (z : Obj) :
    ∃ i x, olderIndexedSplitNodeMap hπ data D j hj r hr hk0 hk hp i x = z := by
  obtain ⟨i, x, hx⟩ := olderIndexedNodeMap_cover hπ data D j hj r hr hk0 hk z
  have hz : z ∈ Set.range (olderIndexedSplitNodeMap hπ data D j hj r hr hk0 hk hp i) := by
    rw [olderIndexedSplitNodeMap_range]
    exact ⟨x, hx⟩
  obtain ⟨y, hy⟩ := hz
  exact ⟨i, y, hy⟩

/-- The original retained indexed atlas is refined by two complete affine split nodes. -/
def olderIndexedSplitNodeOpenCover : (Obj).OpenCover where
  I₀ := Fin 2
  X := fun _ => PolygonNodeBranches.node K
  f := olderIndexedSplitNodeMap hπ data D j hj r hr hk0 hk hp
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨olderIndexedSplitNodeMap_cover hπ data D j hj r hr hk0 hk hp,
      olderIndexedSplitNodeMap_isOpenImmersion hπ data D j hj r hr hk0 hk hp⟩

/-- The first split-node origin is the original first global retained section. -/
@[reassoc] theorem olderIndexedSplitNodeMap_first_origin :
    PolygonNodePresentation.aOrigin K ≫
        olderIndexedSplitNodeMap hπ data D j hj r hr hk0 hk hp 0 ≫ G =
      olderGlobalFirstSection hπ data D j hj r hr hk0 hk := by
  rw [olderIndexedSplitNodeMap, Category.assoc, olderIndexedNodeMap_first_global,
    ← Category.assoc]
  change (PolygonNodePresentation.aOrigin K ≫
    (middleNodeIsoOfZero c (retainedNode_constant_zero data D j hj hp)).hom) ≫ _ = _
  rw [middleNodeIsoOfZero_origin, olderGlobalFirstNode_origin]

/-- The opposite split-node origin is the original second global retained section. -/
@[reassoc] theorem olderIndexedSplitNodeMap_second_origin :
    PolygonNodePresentation.aOrigin K ≫
        olderIndexedSplitNodeMap hπ data D j hj r hr hk0 hk hp 1 ≫ G =
      olderGlobalSecondSection hπ data D j hj r hr hk0 hk := by
  rw [olderIndexedSplitNodeMap, Category.assoc, olderIndexedNodeMap_second_global,
    ← Category.assoc]
  change (PolygonNodePresentation.aOrigin K ≫
    (middleNodeIsoOfZero c (retainedNode_constant_zero data D j hj hp)).hom) ≫ _ = _
  rw [middleNodeIsoOfZero_origin, olderGlobalSecondNode_origin]

end FLT.Mazur.WeierstrassDividedDepth
