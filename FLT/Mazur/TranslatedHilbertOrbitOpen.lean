/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertSourceIntersection
public import FLT.Mazur.TranslatedHilbertOpenBaseChange
public import FLT.Mazur.SmoothHilbertInvariantQuotient

/-!
# Actual translated Hilbert opens in the original orbit quotient

The chart's source intersection is invariant under the original relation.
Its orbit image is therefore an actual quotient open, with precisely the
original open source intersection as inverse image. No coverage is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (i : TranslatedHilbertIndex f)

/-- The actual source open defined by the translated Hilbert chart. -/
def translatedSourceOpen : (smoothHilbertSource f).left.Opens :=
  (translatedSourceInclusion f hL i).left.opensRange

/-- Membership in the source chart is unchanged along the original Picard relation. -/
theorem translatedSourceOpen_invariant :
    (smoothHilbertRelationFst f hL).left ⁻¹ᵁ translatedSourceOpen f hL i =
      (smoothHilbertRelationSnd f hL).left ⁻¹ᵁ translatedSourceOpen f hL i := by
  dsimp only [translatedSourceOpen, translatedSourceInclusion]
  rw [translatedOpen_preimage f hL, translatedOpen_preimage f hL,
    smoothHilbertRelation_class]

/-- The source open with its proved invariance, not an assumed quotient chart. -/
def translatedInvariantSourceOpen :
    InvariantOpens (smoothHilbertRelationFst f hL) (smoothHilbertRelationSnd f hL) :=
  ⟨translatedSourceOpen f hL i, translatedSourceOpen_invariant f hL i⟩

/-- The concrete translated chart determines an actual open of the orbit quotient. -/
def translatedOrbitOpen : Opens (Orbit (smoothHilbertEquivalenceRelation f hL)) :=
  descendOpen (smoothHilbertEquivalenceRelation f hL) (translatedInvariantSourceOpen f hL i)

/-- The descended open has exactly the original chart intersection as source inverse image. -/
theorem translatedOrbitOpen_preimage :
    projection (smoothHilbertEquivalenceRelation f hL) ⁻¹' translatedOrbitOpen f hL i =
      (translatedSourceOpen f hL i : Set _) :=
  invariant_saturation (smoothHilbertEquivalenceRelation f hL)
    (translatedInvariantSourceOpen f hL i)

/-- A source point belongs to the quotient chart exactly when it belongs to the source chart. -/
theorem mem_translatedOrbitOpen_iff (x : (smoothHilbertSource f).left) :
    projection (smoothHilbertEquivalenceRelation f hL) x ∈ translatedOrbitOpen f hL i ↔
      x ∈ translatedSourceOpen f hL i :=
  Set.ext_iff.mp (translatedOrbitOpen_preimage f hL i) x

/-- The actual open source maps continuously into the descended quotient open. -/
def translatedSourceOrbitMap :
    C((translatedSourceIntersection f hL i).left, translatedOrbitOpen f hL i) where
  toFun x := ⟨projection (smoothHilbertEquivalenceRelation f hL)
    ((translatedSourceInclusion f hL i).left x),
    (mem_translatedOrbitOpen_iff f hL i _).mpr ⟨x, rfl⟩⟩
  continuous_toFun := (projection_continuous (smoothHilbertEquivalenceRelation f hL)).comp
    (translatedSourceInclusion f hL i).left.continuous |>.subtype_mk _

/-- Every point of the descended open comes from the original source intersection. -/
theorem translatedSourceOrbitMap_surjective :
    Function.Surjective (translatedSourceOrbitMap f hL i) := by
  rintro ⟨z, hz⟩
  obtain ⟨x, ⟨y, rfl⟩, hx⟩ := hz
  exact ⟨y, Subtype.ext hx⟩

end FLT.Mazur.HilbertChart
