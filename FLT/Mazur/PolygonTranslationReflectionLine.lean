/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonTranslationMarkingLine
public import FLT.Mazur.PolygonReflectionMarkingLine
public import FLT.Mazur.PolygonScalarReflectionRelations
public import FLT.Mazur.DivisorLineSectionIdealTransport
public import FLT.Mazur.TensorPowerPullbackSquare

/-!
# Dihedral coherence of the actual translation marking line

Reflection conjugates full translation to inverse translation on the actual
marked line. The equality includes the canonical ideal reindexing, not merely
an equality of line classes. Every tensor power retains the same square.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonMarkedSections
open PolygonPinching PolygonSinglePointLineNormalization FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] polygonReflection PolygonActionTranslation.translation
  tensorPowerPullbackComparison
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- The two dihedral expressions give the same original marked Cartier ideal. -/
theorem reflectedTranslationIdeal_eq (c : Kˣ) (b : ZMod n) (a : Kˣ) (i : Fin n) :
    (sectionMap K n p (c * a)⁻¹ (reflectIndex (rotateIndex b i))).ker =
      (sectionMap K n p (c⁻¹ * a⁻¹) (rotateIndex (-b) (reflectIndex i))).ker := by
  rw [mul_inv, reflectIndex_rotateIndex]

/-- Inverse translation with the canonical equality of its target marking retained. -/
irreducible_def inverseTranslationLineIso (c : Kˣ) (b : ZMod n) (a : Kˣ) (i : Fin n) :
    (Scheme.Modules.pullback
        (PolygonActionTranslation.translation K n hn p q h c⁻¹ (-b)).left).obj
      (pointLine K n hn p q h (c * a)⁻¹ (reflectIndex (rotateIndex b i))) ≅
        pointLine K n hn p q h a⁻¹ (reflectIndex i) :=
  (Scheme.Modules.pullback _).mapIso
    (divisorLineBundleEqIso (reflectedTranslationIdeal_eq K n p c b a i)
      (section_cartier K n p hn q h (c * a)⁻¹ (reflectIndex (rotateIndex b i))).1
      (section_cartier K n p hn q h (c⁻¹ * a⁻¹) (rotateIndex (-b) (reflectIndex i))).1) ≪≫
    translationLineIso K n hn p q h c⁻¹ (-b) a⁻¹ (reflectIndex i)

/-- Reindexing inverse translation preserves the actual canonical section. -/
theorem inverseTranslationLineIso_section (c : Kˣ) (b : ZMod n) (a : Kˣ) (i : Fin n) :
    DivisorLineSectionCompatible
      (PolygonActionTranslation.translation K n hn p q h c⁻¹ (-b)).left
      (section_cartier K n p hn q h (c * a)⁻¹ (reflectIndex (rotateIndex b i))).1
      (section_cartier K n p hn q h a⁻¹ (reflectIndex i)).1
      (inverseTranslationLineIso K n hn p q h c b a i) := by
  rw [inverseTranslationLineIso_def]
  exact (translationLineIso_section K n hn p q h c⁻¹ (-b) a⁻¹ (reflectIndex i)).sourceIdealEq
    (reflectedTranslationIdeal_eq K n p c b a i)

/-- The complete underlying scheme maps satisfy the original dihedral relation. -/
theorem translation_reflection_left (c : Kˣ) (b : ZMod n) :
    (PolygonActionTranslation.translation K n hn p q h c b).left ≫
        (polygonReflection K hn p q h).left =
      (polygonReflection K hn p q h).left ≫
        (PolygonActionTranslation.translation K n hn p q h c⁻¹ (-b)).left :=
  congrArg Over.Hom.left (translation_reflection K hn p q h c b)

/-- Reflection conjugates the actual full-translation line comparison to its inverse. -/
theorem translationLineIso_reflection (c : Kˣ) (b : ZMod n) (a : Kˣ) (i : Fin n) :
    LinePullbackSquare (PolygonActionTranslation.translation K n hn p q h c b).left
      (polygonReflection K hn p q h).left (polygonReflection K hn p q h).left
      (PolygonActionTranslation.translation K n hn p q h c⁻¹ (-b)).left
      (translation_reflection_left K n hn p q h c b)
      (reflectionLineIso K n hn p q h (c * a) (rotateIndex b i))
      (translationLineIso K n hn p q h c b a i)
      (inverseTranslationLineIso K n hn p q h c b a i)
      (reflectionLineIso K n hn p q h a i) :=
  divisorLineSectionCompatible_square _ _ _ _ _
    (reflectionLineIso_section K n hn p q h (c * a) (rotateIndex b i))
    (translationLineIso_section K n hn p q h c b a i)
    (inverseTranslationLineIso_section K n hn p q h c b a i)
    (reflectionLineIso_section K n hn p q h a i)

/-- The complete dihedral relation holds on every actual marking-line tensor power. -/
theorem translationLineIso_reflection_power
    (c : Kˣ) (b : ZMod n) (a : Kˣ) (i : Fin n) (d : ℕ) :
    LinePullbackSquare (PolygonActionTranslation.translation K n hn p q h c b).left
      (polygonReflection K hn p q h).left (polygonReflection K hn p q h).left
      (PolygonActionTranslation.translation K n hn p q h c⁻¹ (-b)).left
      (translation_reflection_left K n hn p q h c b)
      (tensorPowerPullbackComparison _
        (reflectionLineIso K n hn p q h (c * a) (rotateIndex b i)) d)
      (tensorPowerPullbackComparison _ (translationLineIso K n hn p q h c b a i) d)
      (tensorPowerPullbackComparison _ (inverseTranslationLineIso K n hn p q h c b a i) d)
      (tensorPowerPullbackComparison _ (reflectionLineIso K n hn p q h a i) d) :=
  (translationLineIso_reflection K n hn p q h c b a i).tensorPower d

end FLT.Mazur.PolygonMarkedSections
