/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialGlobalResidueNodes

/-!
# The two-node refinement of the exact initial global index

The two differently oriented full node algebras cover the last indexed object.
Their maps retain the already constructed original global inclusions.
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
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ n)
  (hstart : 0 < start) (hk : 2 * start ≤ depth)
open WeierstrassModificationX
local notation "K" => ResidueField R
local notation "d₀" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 d₀)
local notation "v" => finiteInitialTensorAtlasIso hπ data K j hj
local notation "firstNode" => residueFullFirstNodeChart D start hstart hk
  (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) (Data.factor3 d₀) (Data.factor4 d₀)
local notation "secondNode" => residueFullSecondNodeChart D start hstart hk
  (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) (Data.factor3 d₀) (Data.factor4 d₀)
local notation "Obj" => globalTensorAtlasObject hπ data K j hj
  (Fin.succ (Fin.mk (j + 1) (by omega)))

/-- The two full node schemes with their ordered tangent coefficients. -/
def initialIndexedNodeObject (i : Fin 2) : Scheme :=
  Fin.cases (Spec (.of (FullNodeOpen a c))) (fun _ => Spec (.of (FullNodeOpen (-a) c))) i

/-- Both ordered nodes embed in the original last global indexed object. -/
def initialIndexedNodeMap (i : Fin 2) : initialIndexedNodeObject data i ⟶ Obj :=
  Fin.cases (firstNode ≫ (v).hom) (fun _ => secondNode ≫ (v).hom) i

instance initialIndexedNodeMap_isOpenImmersion (i : Fin 2) :
    IsOpenImmersion (initialIndexedNodeMap hπ data D j hj hstart hk i) := by
  cases i using Fin.cases with
  | zero => change IsOpenImmersion (_ ≫ (v).hom); infer_instance
  | succ i => change IsOpenImmersion (_ ≫ (v).hom); infer_instance

omit [IsBezout R] in
/-- The two constructed node schemes cover the exact initial indexed object. -/
theorem initialIndexedNodeMap_cover (z : Obj) :
    ∃ i x, initialIndexedNodeMap hπ data D j hj hstart hk i x = z := by
  have hv : (v).hom ((v).inv z) = z := congrArg (fun f => f z) (v).inv_hom_id
  rcases residue_fullNodeCharts_cover D start hstart hk
    (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) (Data.factor3 d₀) (Data.factor4 d₀) ((v).inv z) with
    ⟨t, ht⟩ | ⟨t, ht⟩
  · exact ⟨0, t, (congrArg (v).hom ht).trans hv⟩
  · exact ⟨1, t, (congrArg (v).hom ht).trans hv⟩

/-- The complete initial indexed chart has an actual two-node open cover. -/
def initialIndexedNodeOpenCover : (Obj).OpenCover where
  I₀ := Fin 2
  X := initialIndexedNodeObject data
  f := initialIndexedNodeMap hπ data D j hj hstart hk
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨initialIndexedNodeMap_cover hπ data D j hj hstart hk,
      initialIndexedNodeMap_isOpenImmersion hπ data D j hj hstart hk⟩

/-- The first indexed refinement retains its entire original projective map. -/
theorem initialIndexedNodeMap_first_global :
    initialIndexedNodeMap hπ data D j hj hstart hk 0 ≫
      globalTensorAtlasMap hπ data K j hj (Fin.succ ⟨j + 1, by omega⟩) =
        initialGlobalResidueFirstNode hπ data D j hj hstart hk := by
  change ((firstNode) ≫ (v).hom) ≫ _ = _
  rw [Category.assoc, globalInitialTensorChart_eq_index]
  rfl

/-- The opposite indexed refinement retains its entire original projective map. -/
theorem initialIndexedNodeMap_second_global :
    initialIndexedNodeMap hπ data D j hj hstart hk 1 ≫
      globalTensorAtlasMap hπ data K j hj (Fin.succ ⟨j + 1, by omega⟩) =
        initialGlobalResidueSecondNode hπ data D j hj hstart hk := by
  change ((secondNode) ≫ (v).hom) ≫ _ = _
  rw [Category.assoc, globalInitialTensorChart_eq_index]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
