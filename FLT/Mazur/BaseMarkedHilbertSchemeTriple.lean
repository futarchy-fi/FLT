/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertCocycle
public import FLT.Mazur.PullbackRotationTransport
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

/-- The canonical comparison between relative and underlying scheme triple intersections. -/
abbrev baseMarkedSchemeTripleIso :=
  PreservesPullback.iso (Over.forget (Spec (.of R)))
    (baseMarkedChartOverlapLeft f hL V i j) (baseMarkedChartOverlapLeft f hL V i k)

/-- Rotate the full triple intersection in the category of schemes. -/
def baseMarkedSchemeRotate :
    pullback (baseMarkedChartOverlapLeft f hL V i j).left
        (baseMarkedChartOverlapLeft f hL V i k).left ⟶
      pullback (baseMarkedChartOverlapLeft f hL V j k).left
        (baseMarkedChartOverlapLeft f hL V j i).left :=
  mappedPullbackRotation (Over.forget (Spec (.of R)))
    (baseMarkedChartOverlapLeft f hL V i j) (baseMarkedChartOverlapLeft f hL V i k)
    (baseMarkedChartOverlapLeft f hL V j k) (baseMarkedChartOverlapLeft f hL V j i)
    (baseMarkedTripleRotate f hL V i j k)

/-- The scheme-level rotation has the required actual overlap projection. -/
theorem baseMarkedSchemeRotate_snd :
    baseMarkedSchemeRotate f hL V i j k ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ (baseMarkedChartOverlapSwap f hL V i j).left :=
  mappedPullbackRotation_snd (Over.forget (Spec (.of R))) _ _ _ _ _ _
    (baseMarkedTripleRotate_snd f hL V i j k)

end FLT.Mazur.HilbertChart
