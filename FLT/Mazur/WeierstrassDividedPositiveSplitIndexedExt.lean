/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitRetainedNodeExt
public import FLT.Mazur.WeierstrassDividedZeroCycleIndexedExt

/-!
# Every original retained atlas chart is determined by cyclic agreement

The actual two-node covers turn full-node uniqueness into equality on each
original indexed object. The first retained and terminal charts are included.
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
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
variable {Y : Scheme.{u}}
  (f g : finiteGlobalTensorModel hπ data (ResidueField R) (s + 1) hs ⟶ Y)
  (h : ∀ i, (positiveSplitCycleComponent hπ data D s hs hstart hk hp i).left ≫ f =
    (positiveSplitCycleComponent hπ data D s hs hstart hk hp i).left ≫ g)

include h in
/-- The two full nodes detect every original retained chart, including the terminal pair. -/
theorem positiveSplitCycleComponent_retained_indexed_hom_ext (j : Fin (s + 1)) :
    globalTensorAtlasMap hπ data K (s + 1) hs ⟨s - j.val + 2, by omega⟩ ≫ f =
      globalTensorAtlasMap hπ data K (s + 1) hs ⟨s - j.val + 2, by omega⟩ ≫ g := by
  apply globalTensorAtlasMap_hom_ext_of_transport hπ data
    (a := j.val + 1 + (s - j.val)) (by omega) hs (by omega)
    (Fin.succ ⟨s - j.val + 1, by omega⟩) _ (by rfl)
  apply (olderIndexedNodeOpenCover hπ data D j.val (by omega)
    (s - j.val) (by omega) (by omega) (by omega)).hom_ext
  intro i
  change Fin 2 at i
  fin_cases i
  · change olderIndexedNodeMap _ _ _ _ _ _ _ _ _ 0 ≫ _ =
      olderIndexedNodeMap _ _ _ _ _ _ _ _ _ 0 ≫ _
    simp only [olderIndexedNodeMap_first_global_assoc]
    exact positiveSplitCycleComponent_retained_first_hom_ext
      hπ data D s hs hstart hk hp f g h j
  · change olderIndexedNodeMap _ _ _ _ _ _ _ _ _ 1 ≫ _ =
      olderIndexedNodeMap _ _ _ _ _ _ _ _ _ 1 ≫ _
    simp only [olderIndexedNodeMap_second_global_assoc]
    exact positiveSplitCycleComponent_retained_second_hom_ext
      hπ data D s hs hstart hk hp f g h j

end FLT.Mazur.WeierstrassDividedDepth
