/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonActionTranslation

/-!
# Translation on normalization and node images

The actual translation automorphism rotates the images of the normalization
components and the nodes. The one-component specialization fixes its sole image.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.PolygonTranslationImages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open PolygonPinching PolygonActionTranslation
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
variable {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
/-- The automorphism induced by a smooth-group point. -/
def translationIso (a : Kˣ) (b : ZMod n) : C ≅ C :=
  polygonScalingIso K hn p q h a ≪≫ polygonRotationIso K hn p q h b
@[simp] theorem translationIso_hom (a : Kˣ) (b : ZMod n) :
    (translationIso K n hn p q h a b).hom = translation K n hn p q h a b :=
  (translation_eq K n hn p q h a b).symm

theorem component_image (a : Kˣ) (b : ZMod n) (i : Fin n) :
    (translation K n hn p q h a b).left '' Set.range (componentι K n i ≫ p).left =
      Set.range (componentι K n (rotateIndex b i) ≫ p).left := by
  rw [← Set.range_comp]
  change Set.range ((componentι K n i ≫ p) ≫ translation K n hn p q h a b).left = _
  rw [Category.assoc, component_translation]
  change Set.range ((componentι K n (rotateIndex b i) ≫ p).left ∘
    (ProjectiveLine.scalingOver K a).left) = _
  have hi : IsIso (ProjectiveLine.scalingOver K a).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (ProjectiveLine.scalingOverIso K a).hom))
  exact (ProjectiveLine.scalingOver K a).left.homeomorph.surjective.range_comp _

theorem node_image (a : Kˣ) (b : ZMod n) (i : Fin n) :
    (translation K n hn p q h a b).left '' Set.range (nodeι K n i ≫ q).left =
      Set.range (nodeι K n (rotateIndex b i) ≫ q).left := by
  rw [← Set.range_comp]
  change Set.range ((nodeι K n i ≫ q) ≫ translation K n hn p q h a b).left = _
  rw [Category.assoc, node_translation]

theorem one_component_image (hn : 0 < 1)
    {C : Over (Spec (.of K))} (p : components K 1 ⟶ C) (q : nodes K 1 ⟶ C)
    (h : IsPushout (toComponents K 1 hn) (toNodes K 1) p q) (a : Kˣ) (b : ZMod 1) :
    (translation K 1 hn p q h a b).left '' Set.range (componentι K 1 0 ≫ p).left =
      Set.range (componentι K 1 0 ≫ p).left := by
  simpa only [rotateIndex_one] using component_image K 1 hn p q h a b 0
end FLT.Mazur.PolygonTranslationImages
