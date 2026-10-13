/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonMarkingBaseChange
public import FLT.Mazur.PolygonMarkingNormalizationLine
public import FLT.Mazur.RelativeCartierMorphismBaseChange

/-!
# All original normalization component lines after arbitrary base change

Each original projective component carries its pulled Cartier marking ideal.
The comparison with the original polygon line commutes with arbitrary base
change, uniformly for marked and unmarked components.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonMarkingBaseChange
open PolygonPinching PolygonMarkedSections PolygonSinglePointLineNormalization FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Kˣ) (j i : Fin n)

include h in
/-- The marking ideal on every original normalization component is relative Cartier. -/
theorem normalizationIdeal_relativeCartier :
    RelativeEffectiveCartier (component K).hom
      ((sectionMap K n p a j).ker.comap (componentι K n i ≫ p).left) :=
  ⟨normalizationIdeal_cartier K n hn p q h a j i, inferInstance⟩

variable {T : Scheme} (g : T ⟶ Spec (.of K))

/-- The actual positive line of the marking on an original base-changed component. -/
def normalizationMarkingLine : ((Over.pullback g).obj (component K)).left.Modules :=
  divisorLineBundle _ (relativeCartierBaseChange (component K).hom g _
    (normalizationIdeal_relativeCartier K n hn p q h a j i)).1

/-- The actual comparison on every component of the base-changed normalization. -/
irreducible_def normalizationLineIso :
    (Scheme.Modules.pullback ((Over.pullback g).map (componentι K n i ≫ p)).left).obj
      (markingLine K n hn p q h g a j) ≅ normalizationMarkingLine K n hn p q h a j i g :=
  relativeCartierMorphismBaseChangeIso _ g _ _ (section_cartier K n p hn q h a j)
    (normalizationIdeal_relativeCartier K n hn p q h a j i) rfl

/-- The comparison on each original family component preserves the marking section. -/
theorem normalizationLineIso_section :
    DivisorLineSectionCompatible ((Over.pullback g).map (componentι K n i ≫ p)).left
      (markingIdeal_cartier K n hn p q h g a j).1
      (relativeCartierBaseChange (component K).hom g _
        (normalizationIdeal_relativeCartier K n hn p q h a j i)).1
      (normalizationLineIso K n hn p q h a j i g) := by
  rw [normalizationLineIso_def]
  exact relativeCartierMorphismBaseChangeIso_section _ _ _ _ _ _ _

/-- Normalization and arbitrary base change commute on each actual marking line. -/
theorem normalizationLineIso_square :
    LinePullbackSquare ((Over.pullback g).map (componentι K n i ≫ p)).left
      (pullback.fst C.hom g) (pullback.fst (component K).hom g) (componentι K n i ≫ p).left
      (OverPullbackLocalPushout.map_isPullback g (componentι K n i ≫ p)).w
      (markingLineIso K n hn p q h g a j) (normalizationLineIso K n hn p q h a j i g)
      (PolygonSinglePointLineNormalization.normalizationLineIso K n hn p q h a j i)
      (relativeCartierDivisorPullbackIso (component K).hom g _
        (normalizationIdeal_relativeCartier K n hn p q h a j i)) :=
  divisorLineSectionCompatible_square _ _ _ _ _
    (markingLineIso_section K n hn p q h g a j)
    (normalizationLineIso_section K n hn p q h a j i g)
    (PolygonSinglePointLineNormalization.normalizationLineIso_section K n hn p q h a j i)
    (relativeCartierDivisorPullbackIso_section (component K).hom g _
      (normalizationIdeal_relativeCartier K n hn p q h a j i))

end FLT.Mazur.PolygonMarkingBaseChange
