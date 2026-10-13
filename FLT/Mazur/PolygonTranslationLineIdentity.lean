/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonTranslationMarkingLine
public import FLT.Mazur.PolygonTranslationComposition
public import FLT.Mazur.DivisorLineSectionIdealTransport
public import FLT.Mazur.DivisorLineSectionIdentity
public import FLT.Mazur.TensorPowerPullbackSquare

/-!
# Identity normalization of the original translation marking comparison

The identity-parameter comparison, including the canonical target reindexing,
is exactly the pullback unitor transported along the actual whole-curve
identity equation. Its tensor powers retain that identification.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonMarkedSections
open PolygonPinching PolygonSinglePointLineNormalization FCurve PolygonActionTranslation
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] translation tensorPowerPullbackComparison
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- The identity parameters give exactly the original marking ideal. -/
theorem unitTranslatedIdeal_eq (a : Kˣ) (i : Fin n) :
    (sectionMap K n p a i).ker = (sectionMap K n p (1 * a) (rotateIndex 0 i)).ker := by
  rw [one_mul, rotateIndex_zero]

/-- The identity translation comparison with its original source marking retained. -/
irreducible_def unitTranslationLineIso (a : Kˣ) (i : Fin n) :
    (Scheme.Modules.pullback (translation K n hn p q h 1 0).left).obj
      (pointLine K n hn p q h a i) ≅ pointLine K n hn p q h a i :=
  (Scheme.Modules.pullback _).mapIso
    (divisorLineBundleEqIso (unitTranslatedIdeal_eq K n p a i)
      (section_cartier K n p hn q h a i).1
      (section_cartier K n p hn q h (1 * a) (rotateIndex 0 i)).1) ≪≫
    translationLineIso K n hn p q h 1 0 a i

/-- The identity comparison preserves the actual canonical section. -/
theorem unitTranslationLineIso_section (a : Kˣ) (i : Fin n) :
    DivisorLineSectionCompatible (translation K n hn p q h 1 0).left
      (section_cartier K n p hn q h a i).1 (section_cartier K n p hn q h a i).1
      (unitTranslationLineIso K n hn p q h a i) := by
  rw [unitTranslationLineIso_def]
  exact (translationLineIso_section K n hn p q h 1 0 a i).sourceIdealEq
    (unitTranslatedIdeal_eq K n p a i)

/-- The identity translation is the identity on the complete original underlying scheme. -/
theorem translation_one_zero_left : (translation K n hn p q h 1 0).left = 𝟙 C.left :=
  congrArg Over.Hom.left (translation_one_zero K n hn p q h)

/-- The original identity comparison is precisely the transported pullback unitor. -/
theorem unitTranslationLineIso_eq (a : Kˣ) (i : Fin n) :
    unitTranslationLineIso K n hn p q h a i =
      (Scheme.Modules.pullbackCongr (translation_one_zero_left K n hn p q h)).app _ ≪≫
        (Scheme.Modules.pullbackId C.left).app (pointLine K n hn p q h a i) :=
  (unitTranslationLineIso_section K n hn p q h a i).eq_id
    (translation_one_zero_left K n hn p q h)

/-- Every tensor power retains the identity normalization and its original transport. -/
theorem unitTranslationLineIso_power_eq (a : Kˣ) (i : Fin n) (d : ℕ) :
    tensorPowerPullbackComparison _ (unitTranslationLineIso K n hn p q h a i) d =
      (Scheme.Modules.pullbackCongr (translation_one_zero_left K n hn p q h)).app _ ≪≫
        tensorPowerPullbackComparison (𝟙 C.left)
          ((Scheme.Modules.pullbackId C.left).app (pointLine K n hn p q h a i)) d := by
  rw [unitTranslationLineIso_eq, tensorPowerPullbackComparison_congr]

end FLT.Mazur.PolygonMarkedSections
