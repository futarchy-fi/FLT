/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonMarkingNormalizationLine
public import FLT.Mazur.PolygonTranslationMarkingLine
public import FLT.Mazur.PolygonReflectionMarkingLine
public import FLT.Mazur.TensorPowerPullbackSquare

/-!
# Full relabeling on every actual normalization component

The canonical translation and reflection comparisons commute with restriction
to every projective normalization component, including the unmarked components.
These are equalities of actual isomorphisms in every tensor degree.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonMarkedSections
open PolygonPinching PolygonSinglePointLineNormalization FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] polygonReflection PolygonActionTranslation.translation
  tensorPowerPullbackComparison divisorLinePullbackIsoOfEq
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- The actual translation square on each complete normalization component. -/
theorem translation_normalization_left (c : Kˣ) (b : ZMod n) (i : Fin n) :
    (componentι K n i ≫ p).left ≫ (PolygonActionTranslation.translation K n hn p q h c b).left =
      ProjectiveLine.scaling K c ≫ (componentι K n (rotateIndex b i) ≫ p).left :=
  congrArg Over.Hom.left (PolygonActionTranslation.component_translation K n hn p q h c b i)

include h in
/-- The original Cartier marking ideals agree across the normalization square. -/
theorem translation_normalization_ideal (c : Kˣ) (b : ZMod n) (a : Kˣ) (j i : Fin n) :
    ((sectionMap K n p (c * a) (rotateIndex b j)).ker.comap
      (componentι K n (rotateIndex b i) ≫ p).left).comap (ProjectiveLine.scaling K c) =
        (sectionMap K n p a j).ker.comap (componentι K n i ≫ p).left := by
  rw [← Scheme.IdealSheafData.comap_comp,
    ← translation_normalization_left K n hn p q h c b i,
    Scheme.IdealSheafData.comap_comp, section_translation_ideal K n hn p q h c b a j]

/-- The canonical translation comparison on each original normalization component. -/
irreducible_def translationNormalizationLineIso (c : Kˣ) (b : ZMod n) (a : Kˣ) (j i : Fin n) :
    (Scheme.Modules.pullback (ProjectiveLine.scaling K c)).obj
      (divisorLineBundle _
        (normalizationIdeal_cartier K n hn p q h (c * a) (rotateIndex b j) (rotateIndex b i))) ≅
      divisorLineBundle _ (normalizationIdeal_cartier K n hn p q h a j i) := by
  let ht := normalizationIdeal_cartier K n hn p q h (c * a) (rotateIndex b j) (rotateIndex b i)
  let hs := normalizationIdeal_cartier K n hn p q h a j i
  let w := translation_normalization_ideal K n hn p q h c b a j i
  let _ := idealModulePullbackHom_isIso_of_cartier (ProjectiveLine.scaling K c) ht (w.symm ▸ hs)
  exact divisorLinePullbackIsoOfEq _ ht hs w

/-- Every normalization comparison retains the actual canonical marking section. -/
theorem translationNormalizationLineIso_section (c : Kˣ) (b : ZMod n) (a : Kˣ) (j i : Fin n) :
    DivisorLineSectionCompatible (ProjectiveLine.scaling K c)
      (normalizationIdeal_cartier K n hn p q h (c * a) (rotateIndex b j) (rotateIndex b i))
      (normalizationIdeal_cartier K n hn p q h a j i)
      (translationNormalizationLineIso K n hn p q h c b a j i) := by
  let ht := normalizationIdeal_cartier K n hn p q h (c * a) (rotateIndex b j) (rotateIndex b i)
  let hs := normalizationIdeal_cartier K n hn p q h a j i
  let w := translation_normalization_ideal K n hn p q h c b a j i
  let _ := idealModulePullbackHom_isIso_of_cartier (ProjectiveLine.scaling K c) ht (w.symm ▸ hs)
  rw [translationNormalizationLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- Restriction of the actual full-curve comparison is the canonical component comparison. -/
theorem translationLineIso_normalization (c : Kˣ) (b : ZMod n) (a : Kˣ) (j i : Fin n) :
    LinePullbackSquare (componentι K n i ≫ p).left
      (PolygonActionTranslation.translation K n hn p q h c b).left
      (ProjectiveLine.scaling K c) (componentι K n (rotateIndex b i) ≫ p).left
      (translation_normalization_left K n hn p q h c b i)
      (translationLineIso K n hn p q h c b a j) (normalizationLineIso K n hn p q h a j i)
      (normalizationLineIso K n hn p q h (c * a) (rotateIndex b j) (rotateIndex b i))
      (translationNormalizationLineIso K n hn p q h c b a j i) :=
  divisorLineSectionCompatible_square _ _ _ _ _
    (translationLineIso_section K n hn p q h c b a j)
    (normalizationLineIso_section K n hn p q h a j i)
    (normalizationLineIso_section K n hn p q h (c * a) (rotateIndex b j) (rotateIndex b i))
    (translationNormalizationLineIso_section K n hn p q h c b a j i)

/-- Every actual tensor power retains the full normalization square. -/
theorem translationLineIso_normalization_power
    (c : Kˣ) (b : ZMod n) (a : Kˣ) (j i : Fin n) (d : ℕ) :
    LinePullbackSquare (componentι K n i ≫ p).left
      (PolygonActionTranslation.translation K n hn p q h c b).left
      (ProjectiveLine.scaling K c) (componentι K n (rotateIndex b i) ≫ p).left
      (translation_normalization_left K n hn p q h c b i)
      (tensorPowerPullbackComparison _ (translationLineIso K n hn p q h c b a j) d)
      (tensorPowerPullbackComparison _ (normalizationLineIso K n hn p q h a j i) d)
      (tensorPowerPullbackComparison _
        (normalizationLineIso K n hn p q h (c * a) (rotateIndex b j) (rotateIndex b i)) d)
      (tensorPowerPullbackComparison _
        (translationNormalizationLineIso K n hn p q h c b a j i) d) :=
  (translationLineIso_normalization K n hn p q h c b a j i).tensorPower d

end FLT.Mazur.PolygonMarkedSections
