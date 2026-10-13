/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertFaithfulOrbitCover
public import FLT.Mazur.SmoothTranslationQuotientOpenImmersion

/-!
# The faithful cover's original Hilbert parameter points

The actual retained affine-cover point determines an original parameter.
Its image in the full invariant quotient is exactly the prescribed original
orbit; this equation will survive the subsequent ground refinement.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertFaithfulTestCover
open HilbertChart CartierAbel SchemePicard FCurve RelativeRelationOrbit
open OrderedHilbertAffineEtaleTestCover
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
local notation "T" => smoothHilbertSource f
local notation "s" => smoothHilbertSourceSection f hL
local notation "E" => fun x ↦ Sigma.fst (Sigma.snd (chartData f hL T s x))
local notation "degree" => fun x ↦ Prod.snd (Sigma.fst (chartData f hL T s x))
local notation "c" => fun x ↦ chartClass f hL T s x

/-- The actual Hilbert parameter of the point retained by the original faithful affine cover. -/
def retainedParameter (x : (smoothHilbertSource f).left) :
    (variableHilbertTest f (degree x) (E x)).left :=
  (toOriginalChart f hL T s x).left (data f hL T s x).2.2.2.2

/-- The parameter gives precisely the original orbit, through the full overlap. -/
theorem retainedParameter_orbit (x : (smoothHilbertSource f).left) :
    (smoothTranslationChartToOrbit f hL (degree x) (E x) (c x)
      (retainedParameter f hL x)).val = projection (smoothHilbertEquivalenceRelation f hL) x := by
  have hh := congrArg Subtype.val (smoothTranslationChartToOrbit_parameter f hL
    (degree x) (E x) (c x)
      ((toIntersection f hL T s x).left (data f hL T s x).2.2.2.2))
  change (smoothTranslationChartToOrbit f hL (degree x) (E x) (c x)
    (retainedParameter f hL x)).val = projection (smoothHilbertEquivalenceRelation f hL)
      (arrow f hL T s x (data f hL T s x).2.2.2.2) at hh
  rwa [point_covers] at hh

/-- The same original point equation holds for the actual locally ringed quotient inclusion. -/
theorem retainedParameter_quotient (x : (smoothHilbertSource f).left) :
    (smoothTranslationQuotientInclusion f hL (degree x) (E x) (c x)).base
      (projection (variableChartEquivalenceRelation f hL (degree x) (E x) (c x))
        (retainedParameter f hL x)) = projection (smoothHilbertEquivalenceRelation f hL) x := by
  rw [smoothTranslationQuotientInclusion_projection, retainedParameter_orbit]

end FLT.Mazur.OrderedHilbertFaithfulTestCover
