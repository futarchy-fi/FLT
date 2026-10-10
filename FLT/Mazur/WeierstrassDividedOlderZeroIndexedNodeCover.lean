/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalZeroNodes

/-!
# The two full ordered first nodes refine their exact retained atlas object

The different tangent signs are retained in the two source algebras. Their
open cover maps to the actual global inclusions at every later index r+2.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "F" => WeierstrassModificationX.FiberCoordinate a c
open WeierstrassModificationX
local notation "ha" => D.a₁_unit.map (residue R)
local notation "v" => olderGlobalZeroAtlasIso hπ data D j hj r hr hk0 hk
local notation "Obj" => globalTensorAtlasObject hπ data K (j + 1 + r) hr
  (Fin.succ (Fin.mk (r + 1) (by omega)))


/-- The ordered node source keeps the tangent sign on each branch. -/
def olderZeroIndexedNodeObject (i : Fin 2) : Scheme :=
  Fin.cases (Spec (.of (FullNodeOpen a c))) (fun _ => Spec (.of (FullNodeOpen (-a) c))) i

/-- Both full node charts map to the original retained indexed atlas object. -/
def olderZeroIndexedNodeMap (i : Fin 2) :
    olderZeroIndexedNodeObject data j hj i ⟶ Obj :=
  Fin.cases (fullFirstNodeChart a c ha ≫ (v).hom)
    (fun _ => fullSecondNodeChart a c ha ≫ (v).hom) i

instance olderZeroIndexedNodeMap_isOpenImmersion (i : Fin 2) :
    IsOpenImmersion (olderZeroIndexedNodeMap hπ data D j hj r hr hk0 hk i) := by
  cases i using Fin.cases with
  | zero => change IsOpenImmersion (_ ≫ (v).hom); infer_instance
  | succ i => change IsOpenImmersion (_ ≫ (v).hom); infer_instance

omit [IsBezout R] in
/-- The two original nodes cover every point of the exact retained atlas object. -/
theorem olderZeroIndexedNodeMap_cover (z : Obj) :
    ∃ i x, olderZeroIndexedNodeMap hπ data D j hj r hr hk0 hk i x = z := by
  have hv : (v).hom ((v).inv z) = z := congrArg (fun f => f z) (v).inv_hom_id
  rcases fullNodeCharts_cover a c ha ((v).inv z) with ⟨t, ht⟩ | ⟨t, ht⟩
  · exact ⟨0, t, (congrArg (v).hom ht).trans hv⟩
  · exact ⟨1, t, (congrArg (v).hom ht).trans hv⟩

/-- The complete ordered two-node open cover of the retained first indexed chart. -/
def olderZeroIndexedNodeOpenCover : (Obj).OpenCover where
  I₀ := Fin 2
  X := olderZeroIndexedNodeObject data j hj
  f := olderZeroIndexedNodeMap hπ data D j hj r hr hk0 hk
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨olderZeroIndexedNodeMap_cover hπ data D j hj r hr hk0 hk,
      olderZeroIndexedNodeMap_isOpenImmersion hπ data D j hj r hr hk0 hk⟩

/-- The first cover member has exactly the constructed full global node inclusion. -/
@[reassoc] theorem olderZeroIndexedNodeMap_first_global :
    olderZeroIndexedNodeMap hπ data D j hj r hr hk0 hk 0 ≫
      globalTensorAtlasMap hπ data K (j + 1 + r) hr (Fin.succ ⟨r + 1, by omega⟩) =
        olderGlobalZeroFirstNode hπ data D j hj r hr hk0 hk := by
  change (fullFirstNodeChart a c ha ≫ (v).hom) ≫ _ = _
  rw [Category.assoc, olderGlobalZeroAtlasIso_map]
  rfl

/-- The second cover member keeps the opposite ordered full global node inclusion. -/
@[reassoc] theorem olderZeroIndexedNodeMap_second_global :
    olderZeroIndexedNodeMap hπ data D j hj r hr hk0 hk 1 ≫
      globalTensorAtlasMap hπ data K (j + 1 + r) hr (Fin.succ ⟨r + 1, by omega⟩) =
        olderGlobalZeroSecondNode hπ data D j hj r hr hk0 hk := by
  change (fullSecondNodeChart a c ha ≫ (v).hom) ≫ _ = _
  rw [Category.assoc, olderGlobalZeroAtlasIso_map]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
