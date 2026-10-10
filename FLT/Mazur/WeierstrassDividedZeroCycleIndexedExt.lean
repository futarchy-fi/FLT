/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveExt
public import FLT.Mazur.WeierstrassDividedZeroCycleAttachmentExt
public import FLT.Mazur.WeierstrassDividedOlderIndexedNodeCover
public import FLT.Mazur.WeierstrassDividedOlderZeroIndexedNodeCover

/-!
# Cyclic component agreement on the original retained atlas objects

The ordered node covers promote local pushout uniqueness to uniqueness on
each full original indexed chart. Numerical index transport is explicit.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R

/-- Equality on an indexed atlas map survives a change in spelling of its stage and index. -/
theorem globalTensorAtlasMap_hom_ext_of_transport {a b : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (he : a = b) (i : Fin (a + 3)) (k : Fin (b + 3))
    (hi : i.val = k.val) {Y : Scheme.{u}}
    (f g : finiteGlobalTensorModel hπ data K b hb ⟶ Y)
    (h : globalTensorAtlasMap hπ data K a ha i ≫
        eqToHom (finiteGlobalTensorModel_index_congr hπ data K ha hb he) ≫ f =
      globalTensorAtlasMap hπ data K a ha i ≫
        eqToHom (finiteGlobalTensorModel_index_congr hπ data K ha hb he) ≫ g) :
    globalTensorAtlasMap hπ data K b hb k ≫ f =
      globalTensorAtlasMap hπ data K b hb k ≫ g := by
  subst b
  have hi' : i = k := Fin.ext hi
  subst k
  simpa only [eqToHom_refl, Category.id_comp] using h

variable {Y : Scheme.{u}}
  (f g : finiteGlobalTensorModel hπ data (ResidueField R) (s + 1) hs ⟶ Y)
  (h : ∀ i, (zeroSplitCycleComponent hπ data D s hs hstart hk hp i).left ≫ f =
    (zeroSplitCycleComponent hπ data D s hs hstart hk hp i).left ≫ g)

include h in
/-- Component agreement determines each original positive-depth retained indexed chart. -/
theorem zeroSplitCycleComponent_positive_indexed_hom_ext (j : Fin s) :
    globalTensorAtlasMap hπ data K (s + 1) hs ⟨s - j.val + 1, by omega⟩ ≫ f =
      globalTensorAtlasMap hπ data K (s + 1) hs ⟨s - j.val + 1, by omega⟩ ≫ g := by
  apply globalTensorAtlasMap_hom_ext_of_transport hπ data
    (a := j.val + 2 + (s - (j.val + 1))) (by omega) hs (by omega)
    (Fin.succ ⟨s - (j.val + 1) + 1, by omega⟩) _ (by dsimp; omega)
  apply (olderIndexedNodeOpenCover hπ data D (j.val + 1) (by omega)
    (s - (j.val + 1)) (by omega) (by omega) (by omega)).hom_ext
  intro i
  change Fin 2 at i
  fin_cases i
  · change olderIndexedNodeMap _ _ _ _ _ _ _ _ _ 0 ≫ _ =
      olderIndexedNodeMap _ _ _ _ _ _ _ _ _ 0 ≫ _
    simp only [olderIndexedNodeMap_first_global_assoc]
    exact zeroSplitCycleComponent_positive_first_hom_ext hπ data D s hs hstart hk hp j f g h
  · change olderIndexedNodeMap _ _ _ _ _ _ _ _ _ 1 ≫ _ =
      olderIndexedNodeMap _ _ _ _ _ _ _ _ _ 1 ≫ _
    simp only [olderIndexedNodeMap_second_global_assoc]
    exact zeroSplitCycleComponent_positive_second_hom_ext hπ data D s hs hstart hk hp j f g h

include h in
/-- Both original localized start-zero nodes determine the full oldest retained chart. -/
theorem zeroSplitCycleComponent_zero_indexed_hom_ext :
    globalTensorAtlasMap hπ data K (s + 1) hs ⟨s + 2, by omega⟩ ≫ f =
      globalTensorAtlasMap hπ data K (s + 1) hs ⟨s + 2, by omega⟩ ≫ g := by
  apply globalTensorAtlasMap_hom_ext_of_transport hπ data
    (a := 0 + 1 + s) (by omega) hs (by omega)
    (Fin.succ ⟨s + 1, by omega⟩) _ (by rfl)
  apply (olderZeroIndexedNodeOpenCover hπ data D 0 (by omega) s (by omega)
    (by omega) (by omega)).hom_ext
  intro i
  change Fin 2 at i
  fin_cases i
  · change olderZeroIndexedNodeMap _ _ _ _ _ _ _ _ _ 0 ≫ _ =
      olderZeroIndexedNodeMap _ _ _ _ _ _ _ _ _ 0 ≫ _
    simp only [olderZeroIndexedNodeMap_first_global_assoc]
    exact zeroSplitCycleComponent_first_attachment_hom_ext hπ data D s hs hstart hk hp f g h
  · change olderZeroIndexedNodeMap _ _ _ _ _ _ _ _ _ 1 ≫ _ =
      olderZeroIndexedNodeMap _ _ _ _ _ _ _ _ _ 1 ≫ _
    simp only [olderZeroIndexedNodeMap_second_global_assoc]
    exact zeroSplitCycleComponent_second_attachment_hom_ext hπ data D s hs hstart hk hp f g h

end FLT.Mazur.WeierstrassDividedDepth
