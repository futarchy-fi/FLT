/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonMarkingBaseChange
public import FLT.Mazur.PolygonTranslationMarkingLine
public import FLT.Mazur.RelativeCartierMorphismBaseChange

/-!
# Full translation of the original marking line after arbitrary base change

Translation on the original base-changed polygon preserves the actual marked
ideal and canonical section. Its line comparison commutes with base change.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonMarkingBaseChange
open PolygonPinching PolygonMarkedSections FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonActionTranslation.translation
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  {T : Scheme} (g : T ⟶ Spec (.of K)) (c : Kˣ) (b : ZMod n) (a : Kˣ) (i : Fin n)

/-- The complete family translation preserves the full original marked ideal. -/
theorem translation_ideal :
    (markingIdeal K n p g (c * a) (rotateIndex b i)).comap
        ((Over.pullback g).map (PolygonActionTranslation.translation K n hn p q h c b)).left =
      markingIdeal K n p g a i :=
  relativeCartierMorphismBaseChange_ideal _ g _ _
    (section_translation_ideal K n hn p q h c b a i)

/-- The full family translation compares the actual positive marking lines. -/
irreducible_def translationLineIso :
    (Scheme.Modules.pullback
      ((Over.pullback g).map (PolygonActionTranslation.translation K n hn p q h c b)).left).obj
        (markingLine K n hn p q h g (c * a) (rotateIndex b i)) ≅
      markingLine K n hn p q h g a i :=
  relativeCartierMorphismBaseChangeIso _ g _ _
    (section_cartier K n p hn q h (c * a) (rotateIndex b i))
    (section_cartier K n p hn q h a i) (section_translation_ideal K n hn p q h c b a i)

/-- Translation preserves the original family marking's canonical section. -/
theorem translationLineIso_section :
    DivisorLineSectionCompatible
      ((Over.pullback g).map (PolygonActionTranslation.translation K n hn p q h c b)).left
      (markingIdeal_cartier K n hn p q h g (c * a) (rotateIndex b i)).1
      (markingIdeal_cartier K n hn p q h g a i).1
      (translationLineIso K n hn p q h g c b a i) := by
  rw [translationLineIso_def]
  exact relativeCartierMorphismBaseChangeIso_section _ _ _ _ _ _ _

/-- Original translation and arbitrary base change commute on the actual positive lines. -/
theorem translationLineIso_square :
    LinePullbackSquare
      ((Over.pullback g).map (PolygonActionTranslation.translation K n hn p q h c b)).left
      (pullback.fst C.hom g) (pullback.fst C.hom g)
      (PolygonActionTranslation.translation K n hn p q h c b).left
      (OverPullbackLocalPushout.map_isPullback g
        (PolygonActionTranslation.translation K n hn p q h c b)).w
      (markingLineIso K n hn p q h g (c * a) (rotateIndex b i))
      (translationLineIso K n hn p q h g c b a i)
      (PolygonMarkedSections.translationLineIso K n hn p q h c b a i)
      (markingLineIso K n hn p q h g a i) :=
  divisorLineSectionCompatible_square _ _ _ _ _
    (markingLineIso_section K n hn p q h g (c * a) (rotateIndex b i))
    (translationLineIso_section K n hn p q h g c b a i)
    (PolygonMarkedSections.translationLineIso_section K n hn p q h c b a i)
    (markingLineIso_section K n hn p q h g a i)

end FLT.Mazur.PolygonMarkingBaseChange
