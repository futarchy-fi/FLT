/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityCycleEndCharts
public import FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoAttachmentExt
public import FLT.Mazur.WeierstrassDividedOlderZeroIndexedNodeCover
public import FLT.Mazur.WeierstrassDividedZeroEqualityCocone

/-!
# The original length-two equality cycle detects arbitrary scheme morphisms

The four original finite atlas objects are checked using the complete
terminal Laurent chart, the exterior, and both full initial attachments.
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
  (D : SplitNodeDepth W π depth) (hs : 0 + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + 0 + 1) ≤ depth)
  (hp : 2 * (start + 0 + 1) = depth)
local notation "K" => ResidueField R
variable {Y : Scheme.{u}}
  (f g : finiteGlobalTensorModel hπ data (ResidueField R) (0 + 1) hs ⟶ Y)
  (h : ∀ i, (zeroEqualityCycleComponent hπ data D 0 hs hstart hk hp i).left ≫ f =
    (zeroEqualityCycleComponent hπ data D 0 hs hstart hk hp i).left ≫ g)

include h in
/-- The original horizontal atlas object is determined by the two actual components. -/
theorem zeroEqualityCycleComponent_lengthTwo_indexed_hom_ext :
    globalTensorAtlasMap hπ data K (0 + 1) hs ⟨2, by omega⟩ ≫ f =
      globalTensorAtlasMap hπ data K (0 + 1) hs ⟨2, by omega⟩ ≫ g := by
  change globalTensorAtlasMap hπ data K (0 + 1 + 0) hs (Fin.succ ⟨0 + 1, by omega⟩) ≫ f =
    globalTensorAtlasMap hπ data K (0 + 1 + 0) hs (Fin.succ ⟨0 + 1, by omega⟩) ≫ g
  apply (olderZeroIndexedNodeOpenCover hπ data D 0 hs 0 hs hstart hk).hom_ext
  intro i
  change Fin 2 at i
  fin_cases i
  · change olderZeroIndexedNodeMap _ _ _ _ _ _ _ _ _ 0 ≫ _ =
      olderZeroIndexedNodeMap _ _ _ _ _ _ _ _ _ 0 ≫ _
    simp only [olderZeroIndexedNodeMap_first_global_assoc]
    exact zeroEqualityCycleComponent_lengthTwo_first_hom_ext hπ data D hs hstart hk hp f g h
  · change olderZeroIndexedNodeMap _ _ _ _ _ _ _ _ _ 1 ≫ _ =
      olderZeroIndexedNodeMap _ _ _ _ _ _ _ _ _ 1 ≫ _
    simp only [olderZeroIndexedNodeMap_second_global_assoc]
    exact zeroEqualityCycleComponent_lengthTwo_second_hom_ext hπ data D hs hstart hk hp f g h

include h in
/-- The complete length-two cycle jointly detects morphisms to every target scheme. -/
theorem zeroEqualityCycleComponent_hom_ext_lengthTwo : f = g := by
  apply (globalTensorOpenCover hπ data K (0 + 1) hs).hom_ext
  intro i
  change Fin 4 at i
  change globalTensorAtlasMap hπ data K (0 + 1) hs i ≫ f =
    globalTensorAtlasMap hπ data K (0 + 1) hs i ≫ g
  fin_cases i
  · exact zeroEqualityCycleComponent_infinity_hom_ext hπ data D 0 hs hstart hk hp f g h
  · exact zeroEqualityCycleComponent_terminal_hom_ext hπ data D 0 hs hstart hk hp f g h
  · exact zeroEqualityCycleComponent_lengthTwo_indexed_hom_ext hπ data D hs hstart hk hp f g h
  · exact zeroEqualityCycleComponent_initial_hom_ext hπ data D 0 hs hstart hk hp f g h

/-- The actual length-two normalization leg is epimorphic over the residue field. -/
theorem zeroEqualityCycleNormalization_epi_lengthTwo :
    Epi (zeroEqualityCycleNormalization hπ data D 0 hs hstart hk hp) where
  left_cancellation f g he := by
    apply Over.OverMorphism.ext
    apply zeroEqualityCycleComponent_hom_ext_lengthTwo hπ data D hs hstart hk hp f.left g.left
    intro i
    have H := congrArg (fun q => PolygonPinching.componentι K (2 * 0 + 2) i ≫ q) he
    simp only [zeroEqualityCycleNormalization_ι_assoc] at H
    exact congrArg Over.Hom.left H

end FLT.Mazur.WeierstrassDividedDepth
