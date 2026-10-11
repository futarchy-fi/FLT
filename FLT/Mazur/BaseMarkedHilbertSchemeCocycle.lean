/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertSchemeTriple
public import FLT.Mazur.PullbackRotationCoordinates
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Scheme-level rotations of base-marked Hilbert intersections

The forgetful functor preserves pullbacks. It transports the already proved
relative triple rotations and projection equations to actual schemes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] baseMarkedTripleRotate baseMarkedTripleRoute
  baseMarkedChartOverlapLeft baseMarkedChartOverlapRight
  baseMarkedChartOverlapSwap baseMarkedChartOverlap variableHilbertTest
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (V : Over (Spec (.of R))) (i j k : BaseMarkedHilbertIndex f V)

/-- The transported first parameter coordinate on the full triple intersection. -/
@[irreducible]
def baseMarkedSchemeFirst :
    pullback (baseMarkedChartOverlapLeft f hL V i j).left
        (baseMarkedChartOverlapLeft f hL V i k).left ⟶
      (variableHilbertTest f i.1 V).left :=
  mappedPullbackCoordinate (Over.forget (Spec (.of R))) _ _
    (baseMarkedTripleFirst f hL V i j k)

/-- The transported second parameter coordinate on the full triple intersection. -/
@[irreducible]
def baseMarkedSchemeSecond :
    pullback (baseMarkedChartOverlapLeft f hL V i j).left
        (baseMarkedChartOverlapLeft f hL V i k).left ⟶
      (variableHilbertTest f j.1 V).left :=
  mappedPullbackCoordinate (Over.forget (Spec (.of R))) _ _
    (baseMarkedTripleSecond f hL V i j k)

/-- The transported third parameter coordinate on the full triple intersection. -/
@[irreducible]
def baseMarkedSchemeThird :
    pullback (baseMarkedChartOverlapLeft f hL V i j).left
        (baseMarkedChartOverlapLeft f hL V i k).left ⟶
      (variableHilbertTest f k.1 V).left :=
  mappedPullbackCoordinate (Over.forget (Spec (.of R))) _ _
    (baseMarkedTripleThird f hL V i j k)

instance baseMarkedSchemeFirst_mono : Mono (baseMarkedSchemeFirst f hL V i j k) := by
  unfold baseMarkedSchemeFirst mappedPullbackCoordinate
  infer_instance

/-- Rotation carries the first coordinate to the second coordinate. -/
@[reassoc]
lemma baseMarkedSchemeRotate_first :
    baseMarkedSchemeRotate f hL V i j k ≫ baseMarkedSchemeFirst f hL V j k i =
      baseMarkedSchemeSecond f hL V i j k := by
  unfold baseMarkedSchemeFirst baseMarkedSchemeSecond
  exact mappedPullbackRotation_coordinate (Over.forget (Spec (.of R))) _ _ _ _ _ _ _
    (baseMarkedTripleRotate_first f hL V i j k)

/-- Rotation carries the second coordinate to the third coordinate. -/
@[reassoc]
lemma baseMarkedSchemeRotate_second :
    baseMarkedSchemeRotate f hL V i j k ≫ baseMarkedSchemeSecond f hL V j k i =
      baseMarkedSchemeThird f hL V i j k := by
  unfold baseMarkedSchemeSecond baseMarkedSchemeThird
  exact mappedPullbackRotation_coordinate (Over.forget (Spec (.of R))) _ _ _ _ _ _ _
    (baseMarkedTripleRotate_second f hL V i j k)

/-- Rotation carries the third coordinate to the first coordinate. -/
@[reassoc]
lemma baseMarkedSchemeRotate_third :
    baseMarkedSchemeRotate f hL V i j k ≫ baseMarkedSchemeThird f hL V j k i =
      baseMarkedSchemeFirst f hL V i j k := by
  unfold baseMarkedSchemeThird baseMarkedSchemeFirst
  exact mappedPullbackRotation_coordinate (Over.forget (Spec (.of R))) _ _ _ _ _ _ _
    (baseMarkedTripleRotate_third f hL V i j k)

/-- Three rotations return the original full scheme-theoretic triple intersection. -/
theorem baseMarkedSchemeRotate_cocycle :
    baseMarkedSchemeRotate f hL V i j k ≫ baseMarkedSchemeRotate f hL V j k i ≫
      baseMarkedSchemeRotate f hL V k i j = 𝟙 _ := by
  apply (cancel_mono (baseMarkedSchemeFirst f hL V i j k)).mp
  rw [Category.assoc, Category.assoc, baseMarkedSchemeRotate_first,
    baseMarkedSchemeRotate_second, baseMarkedSchemeRotate_third, Category.id_comp]

end FLT.Mazur.HilbertChart
