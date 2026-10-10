/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalResidueNodes

/-!
# Two ordered nodes cover each original indexed older chart

The residue node cover is transported through the actual tensor atlas
isomorphism. Its two composite global maps are precisely the already
constructed ordered older nodes, so it can refine the full global cover.
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
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "N" => MiddleNodeOpen (residue R (Data.b6 e))
local notation "v" => olderSuccessiveTensorAtlasIso hπ data K j hj r hr
local notation "a" => residueMiddleFirstNodeChart D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "b" => residueMiddleSecondNodeChart D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "Obj" => globalTensorAtlasObject hπ data K (j + 1 + r) hr
  (Fin.succ (Fin.mk (r + 1) (by omega)))

/-- The first and second ordered node maps into the original older indexed chart. -/
def olderIndexedNodeMap (i : Fin 2) : Spec (.of N) ⟶ Obj :=
  Fin.cases (a ≫ (v).hom) (fun _ => b ≫ (v).hom) i

instance olderIndexedNodeMap_isOpenImmersion (i : Fin 2) :
    IsOpenImmersion (olderIndexedNodeMap hπ data D j hj r hr hk0 hk i) := by
  cases i using Fin.cases with
  | zero => change IsOpenImmersion (_ ≫ (v).hom); infer_instance
  | succ i => change IsOpenImmersion (_ ≫ (v).hom); infer_instance

omit [IsBezout R] in
/-- The exact indexed coefficient pullback is covered by the two ordered residue nodes. -/
theorem olderIndexedNodeMap_cover (z : Obj) :
    ∃ i x, olderIndexedNodeMap hπ data D j hj r hr hk0 hk i x = z := by
  have hv : (v).hom ((v).inv z) = z := congrArg (fun f => f z) (v).inv_hom_id
  rcases residueMiddleNodeCharts_cover D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) ((v).inv z) with
    ⟨t, ht⟩ | ⟨t, ht⟩
  · exact ⟨0, t, (congrArg (v).hom ht).trans hv⟩
  · exact ⟨1, t, (congrArg (v).hom ht).trans hv⟩

/-- The actual two-node refinement of an older indexed global atlas object. -/
def olderIndexedNodeOpenCover : (Obj).OpenCover where
  I₀ := Fin 2
  X := fun _ => Spec (.of N)
  f := olderIndexedNodeMap hπ data D j hj r hr hk0 hk
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨olderIndexedNodeMap_cover hπ data D j hj r hr hk0 hk,
      olderIndexedNodeMap_isOpenImmersion hπ data D j hj r hr hk0 hk⟩

/-- The first member of this refinement retains its constructed global inclusion. -/
@[reassoc] theorem olderIndexedNodeMap_first_global :
    olderIndexedNodeMap hπ data D j hj r hr hk0 hk 0 ≫
      globalTensorAtlasMap hπ data K (j + 1 + r) hr (Fin.succ ⟨r + 1, by omega⟩) =
        olderGlobalResidueFirstNode hπ data D j hj r hr hk0 hk := by
  change (a ≫ (v).hom) ≫ _ = _
  rw [Category.assoc, olderGlobalResidueFirstNode_eq_index]

/-- The second member retains the opposite ordered global inclusion. -/
@[reassoc] theorem olderIndexedNodeMap_second_global :
    olderIndexedNodeMap hπ data D j hj r hr hk0 hk 1 ≫
      globalTensorAtlasMap hπ data K (j + 1 + r) hr (Fin.succ ⟨r + 1, by omega⟩) =
        olderGlobalResidueSecondNode hπ data D j hj r hr hk0 hk := by
  change (b ≫ (v).hom) ≫ _ = _
  rw [Category.assoc, olderGlobalResidueSecondNode_eq_index]

end FLT.Mazur.WeierstrassDividedDepth
