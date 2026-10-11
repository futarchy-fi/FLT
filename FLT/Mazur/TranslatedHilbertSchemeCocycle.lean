/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertSchemeTriple
public import FLT.Mazur.PullbackRotationCoordinates
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Scheme-level rotations of translated Hilbert intersections

The forgetful functor preserves pullbacks. It transports the already proved
relative triple rotations and projection equations to actual schemes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] translatedHilbertTripleRotate translatedHilbertTripleRoute
  translatedHilbertChartOverlapLeft translatedHilbertChartOverlapRight
  translatedHilbertChartOverlapSwap translatedHilbertChartOverlap acyclicHilbertTest
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (i j k : TranslatedHilbertIndex f)

/-- The transported first parameter coordinate on the full triple intersection. -/
@[irreducible]
def translatedHilbertSchemeFirst :
    pullback (translatedHilbertChartOverlapLeft f hL i j).left
        (translatedHilbertChartOverlapLeft f hL i k).left ⟶
      (acyclicHilbertTest f i.1).left :=
  mappedPullbackCoordinate (Over.forget (Spec (.of R))) _ _
    (translatedHilbertTripleFirst f hL i j k)

/-- The transported second parameter coordinate on the full triple intersection. -/
@[irreducible]
def translatedHilbertSchemeSecond :
    pullback (translatedHilbertChartOverlapLeft f hL i j).left
        (translatedHilbertChartOverlapLeft f hL i k).left ⟶
      (acyclicHilbertTest f j.1).left :=
  mappedPullbackCoordinate (Over.forget (Spec (.of R))) _ _
    (translatedHilbertTripleSecond f hL i j k)

/-- The transported third parameter coordinate on the full triple intersection. -/
@[irreducible]
def translatedHilbertSchemeThird :
    pullback (translatedHilbertChartOverlapLeft f hL i j).left
        (translatedHilbertChartOverlapLeft f hL i k).left ⟶
      (acyclicHilbertTest f k.1).left :=
  mappedPullbackCoordinate (Over.forget (Spec (.of R))) _ _
    (translatedHilbertTripleThird f hL i j k)

instance translatedHilbertSchemeFirst_mono : Mono (translatedHilbertSchemeFirst f hL i j k) := by
  unfold translatedHilbertSchemeFirst mappedPullbackCoordinate
  infer_instance

/-- Rotation carries the first coordinate to the second coordinate. -/
@[reassoc]
lemma translatedHilbertSchemeRotate_first :
    translatedHilbertSchemeRotate f hL i j k ≫ translatedHilbertSchemeFirst f hL j k i =
      translatedHilbertSchemeSecond f hL i j k := by
  unfold translatedHilbertSchemeFirst translatedHilbertSchemeSecond
  exact mappedPullbackRotation_coordinate (Over.forget (Spec (.of R))) _ _ _ _ _ _ _
    (translatedHilbertTripleRotate_first f hL i j k)

/-- Rotation carries the second coordinate to the third coordinate. -/
@[reassoc]
lemma translatedHilbertSchemeRotate_second :
    translatedHilbertSchemeRotate f hL i j k ≫ translatedHilbertSchemeSecond f hL j k i =
      translatedHilbertSchemeThird f hL i j k := by
  unfold translatedHilbertSchemeSecond translatedHilbertSchemeThird
  exact mappedPullbackRotation_coordinate (Over.forget (Spec (.of R))) _ _ _ _ _ _ _
    (translatedHilbertTripleRotate_second f hL i j k)

/-- Rotation carries the third coordinate to the first coordinate. -/
@[reassoc]
lemma translatedHilbertSchemeRotate_third :
    translatedHilbertSchemeRotate f hL i j k ≫ translatedHilbertSchemeThird f hL j k i =
      translatedHilbertSchemeFirst f hL i j k := by
  unfold translatedHilbertSchemeThird translatedHilbertSchemeFirst
  exact mappedPullbackRotation_coordinate (Over.forget (Spec (.of R))) _ _ _ _ _ _ _
    (translatedHilbertTripleRotate_third f hL i j k)

/-- Three rotations return the original full scheme-theoretic triple intersection. -/
theorem translatedHilbertSchemeRotate_cocycle :
    translatedHilbertSchemeRotate f hL i j k ≫ translatedHilbertSchemeRotate f hL j k i ≫
      translatedHilbertSchemeRotate f hL k i j = 𝟙 _ := by
  apply (cancel_mono (translatedHilbertSchemeFirst f hL i j k)).mp
  rw [Category.assoc, Category.assoc, translatedHilbertSchemeRotate_first,
    translatedHilbertSchemeRotate_second, translatedHilbertSchemeRotate_third, Category.id_comp]

end FLT.Mazur.HilbertChart
