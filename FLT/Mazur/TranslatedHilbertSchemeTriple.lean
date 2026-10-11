/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertTripleCocycle
public import FLT.Mazur.PullbackRotationTransport
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

/-- The canonical comparison between relative and underlying scheme triple intersections. -/
abbrev translatedHilbertSchemeTripleIso :=
  PreservesPullback.iso (Over.forget (Spec (.of R)))
    (translatedHilbertChartOverlapLeft f hL i j) (translatedHilbertChartOverlapLeft f hL i k)

/-- Rotate the full triple intersection in the category of schemes. -/
def translatedHilbertSchemeRotate :
    pullback (translatedHilbertChartOverlapLeft f hL i j).left
        (translatedHilbertChartOverlapLeft f hL i k).left ⟶
      pullback (translatedHilbertChartOverlapLeft f hL j k).left
        (translatedHilbertChartOverlapLeft f hL j i).left :=
  mappedPullbackRotation (Over.forget (Spec (.of R)))
    (translatedHilbertChartOverlapLeft f hL i j) (translatedHilbertChartOverlapLeft f hL i k)
    (translatedHilbertChartOverlapLeft f hL j k) (translatedHilbertChartOverlapLeft f hL j i)
    (translatedHilbertTripleRotate f hL i j k)

/-- The scheme-level rotation has the required actual overlap projection. -/
theorem translatedHilbertSchemeRotate_snd :
    translatedHilbertSchemeRotate f hL i j k ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ (translatedHilbertChartOverlapSwap f hL i j).left :=
  mappedPullbackRotation_snd (Over.forget (Spec (.of R))) _ _ _ _ _ _
    (translatedHilbertTripleRotate_snd f hL i j k)

end FLT.Mazur.HilbertChart
