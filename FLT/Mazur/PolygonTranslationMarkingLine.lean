/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonScalingMarkingLine
public import FLT.Mazur.PolygonRotationMarkingLine
public import FLT.Mazur.PolygonActionTranslation
public import FLT.Mazur.PolygonSinglePointLineNormalization
public import FLT.Mazur.DivisorLineSectionCompatibility

/-!
# Original marked sections and lines under full polygon translation

Translation multiplies the marking coordinate and relabels its component.
Its cartesian square supplies the Cartier ideal and positive line
comparison, retaining the actual canonical vanishing section.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonMarkedSections
open PolygonPinching PolygonSinglePointLineNormalization FCurve
open ProjectiveLineActionSpecialization
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonActionTranslation.translation
  polygonScaling polygonRotation divisorLinePullbackIsoOfEq
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)


/-- Full translation multiplies the original unit and rotates the component label. -/
@[reassoc] theorem section_translation (c : Kˣ) (b : ZMod n) (a : Kˣ) (i : Fin n) :
    sectionMap K n p a i ≫ (PolygonActionTranslation.translation K n hn p q h c b).left =
      sectionMap K n p (c * a) (rotateIndex b i) := by
  have ht := congrArg Over.Hom.left
    (PolygonActionTranslation.translation_eq K n hn p q h c b)
  change (PolygonActionTranslation.translation K n hn p q h c b).left =
    (polygonScaling K hn p q h c).left ≫ (polygonRotation K hn p q h b).left at ht
  rw [ht, ← Category.assoc, section_scaling, section_rotation]


/-- The translation square of original marked sections is cartesian on the whole polygon. -/
theorem section_translation_square (c : Kˣ) (b : ZMod n) (a : Kˣ) (i : Fin n) :
    IsPullback (𝟙 (Spec (.of K))) (sectionMap K n p a i)
      (sectionMap K n p (c * a) (rotateIndex b i))
      (PolygonActionTranslation.translation K n hn p q h c b).left := by
  let _ : IsIso (polygonScaling K hn p q h c).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (polygonScalingIso K hn p q h c).hom))
  let _ : IsIso (polygonRotation K hn p q h b).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (polygonRotationIso K hn p q h b).hom))
  have ht := congrArg Over.Hom.left
    (PolygonActionTranslation.translation_eq K n hn p q h c b)
  change (PolygonActionTranslation.translation K n hn p q h c b).left =
    (polygonScaling K hn p q h c).left ≫ (polygonRotation K hn p q h b).left at ht
  let _ : IsIso (PolygonActionTranslation.translation K n hn p q h c b).left := by
    rw [ht]
    infer_instance
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, section_translation]⟩


/-- Translation retains the complete Cartier ideal, including the original multiplicity. -/
theorem section_translation_ideal (c : Kˣ) (b : ZMod n) (a : Kˣ) (i : Fin n) :
    (sectionMap K n p (c * a) (rotateIndex b i)).ker.comap
      (PolygonActionTranslation.translation K n hn p q h c b).left =
        (sectionMap K n p a i).ker := by
  let _ := PolygonSeparated.cocone K n hn p q h
  let _ := isClosedImmersion_section C.hom _ (section_base K n p (c * a) (rotateIndex b i))
  have H := (section_translation_square K n hn p q h c b a i).flip
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso H.isoPullback.hom, H.isoPullback_hom_fst]


/-- The actual ideal pullback comparison under translation is invertible. -/
theorem translationIdealComparison_isIso (c : Kˣ) (b : ZMod n) (a : Kˣ) (i : Fin n) :
    IsIso (idealModulePullbackHom (sectionMap K n p (c * a) (rotateIndex b i)).ker
      (PolygonActionTranslation.translation K n hn p q h c b).left) := by
  apply idealModulePullbackHom_isIso_of_cartier _
    (section_cartier K n p hn q h (c * a) (rotateIndex b i)).1
  rw [section_translation_ideal]
  exact (section_cartier K n p hn q h a i).1


/-- Translation pulls the original relabeled positive marking line back to its source line. -/
irreducible_def translationLineIso (c : Kˣ) (b : ZMod n) (a : Kˣ) (i : Fin n) :
    (Scheme.Modules.pullback (PolygonActionTranslation.translation K n hn p q h c b).left).obj
      (pointLine K n hn p q h (c * a) (rotateIndex b i)) ≅ pointLine K n hn p q h a i := by
  let _ := translationIdealComparison_isIso K n hn p q h c b a i
  exact divisorLinePullbackIsoOfEq _
    (section_cartier K n p hn q h (c * a) (rotateIndex b i)).1
    (section_cartier K n p hn q h a i).1 (section_translation_ideal K n hn p q h c b a i)


/-- Translation preserves the original canonical section of the marking line. -/
theorem translationLineIso_section (c : Kˣ) (b : ZMod n) (a : Kˣ) (i : Fin n) :
    DivisorLineSectionCompatible (PolygonActionTranslation.translation K n hn p q h c b).left
      (section_cartier K n p hn q h (c * a) (rotateIndex b i)).1
      (section_cartier K n p hn q h a i).1 (translationLineIso K n hn p q h c b a i) := by
  let _ := translationIdealComparison_isIso K n hn p q h c b a i
  rw [translationLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

end FLT.Mazur.PolygonMarkedSections
