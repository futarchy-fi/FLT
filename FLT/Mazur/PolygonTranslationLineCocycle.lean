/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonTranslationMarkingLine
public import FLT.Mazur.PolygonTranslationComposition
public import FLT.Mazur.DivisorLineSectionIdealTransport
public import FLT.Mazur.DivisorLineSectionTriangle

/-!
# The actual translation cocycle on marking lines

Successive translations compose to the original product-parameter comparison.
The formula keeps the canonical target reindexing and pullback compositor,
and holds for every tensor power of the original marking line.
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

/-- The product and successive-translation expressions retain exactly the same ideal. -/
theorem translatedProductIdeal_eq (c d : Kˣ) (b e : ZMod n) (a : Kˣ) (i : Fin n) :
    (sectionMap K n p ((c * d) * a) (rotateIndex (b + e) i)).ker =
      (sectionMap K n p (d * (c * a)) (rotateIndex e (rotateIndex b i))).ker := by
  rw [rotateIndex_add, mul_comm c d, mul_assoc]

/-- The second comparison with its original product target ideal explicitly retained. -/
irreducible_def translationSecondLineIso
    (c d : Kˣ) (b e : ZMod n) (a : Kˣ) (i : Fin n) :
    (Scheme.Modules.pullback (translation K n hn p q h d e).left).obj
      (pointLine K n hn p q h ((c * d) * a) (rotateIndex (b + e) i)) ≅
        pointLine K n hn p q h (c * a) (rotateIndex b i) :=
  (Scheme.Modules.pullback _).mapIso
    (divisorLineBundleEqIso (translatedProductIdeal_eq K n p c d b e a i)
      (section_cartier K n p hn q h ((c * d) * a) (rotateIndex (b + e) i)).1
      (section_cartier K n p hn q h (d * (c * a)) (rotateIndex e (rotateIndex b i))).1) ≪≫
    translationLineIso K n hn p q h d e (c * a) (rotateIndex b i)

/-- Product reindexing preserves the actual marking section under the second translation. -/
theorem translationSecondLineIso_section
    (c d : Kˣ) (b e : ZMod n) (a : Kˣ) (i : Fin n) :
    DivisorLineSectionCompatible (translation K n hn p q h d e).left
      (section_cartier K n p hn q h ((c * d) * a) (rotateIndex (b + e) i)).1
      (section_cartier K n p hn q h (c * a) (rotateIndex b i)).1
      (translationSecondLineIso K n hn p q h c d b e a i) := by
  rw [translationSecondLineIso_def]
  exact (translationLineIso_section K n hn p q h d e (c * a) (rotateIndex b i)).sourceIdealEq
    (translatedProductIdeal_eq K n p c d b e a i)

/-- Successive translations satisfy the actual marking-line cocycle equation. -/
theorem translationLineIso_cocycle (c d : Kˣ) (b e : ZMod n) (a : Kˣ) (i : Fin n) :
    LinePullbackTriangle (translation K n hn p q h c b).left
      (translation K n hn p q h d e).left (translation K n hn p q h (c * d) (b + e)).left
      (translation_mul_add_left K n hn p q h c d b e)
      (translationSecondLineIso K n hn p q h c d b e a i)
      (translationLineIso K n hn p q h c b a i)
      (translationLineIso K n hn p q h (c * d) (b + e) a i) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (translationSecondLineIso_section K n hn p q h c d b e a i)
    (translationLineIso_section K n hn p q h c b a i)
    (translationLineIso_section K n hn p q h (c * d) (b + e) a i)

/-- The original translation cocycle holds in every marking-line tensor degree. -/
theorem translationLineIso_cocycle_power
    (c d : Kˣ) (b e : ZMod n) (a : Kˣ) (i : Fin n) (m : ℕ) :
    LinePullbackTriangle (translation K n hn p q h c b).left
      (translation K n hn p q h d e).left (translation K n hn p q h (c * d) (b + e)).left
      (translation_mul_add_left K n hn p q h c d b e)
      (tensorPowerPullbackComparison _ (translationSecondLineIso K n hn p q h c d b e a i) m)
      (tensorPowerPullbackComparison _ (translationLineIso K n hn p q h c b a i) m)
      (tensorPowerPullbackComparison _
        (translationLineIso K n hn p q h (c * d) (b + e) a i) m) :=
  (translationLineIso_cocycle K n hn p q h c d b e a i).tensorPower m

end FLT.Mazur.PolygonMarkedSections
