/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertOrbitOpen
public import FLT.Mazur.TranslatedHilbertRestrictedRelation

/-!
# Point fibers of a translated Hilbert quotient chart

The actual chart parameter and actual orbit map have exactly the same point
fibers. Scheme pullbacks supply common extension points; no preservation of
fiber products by the underlying-point functor is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (i : TranslatedHilbertIndex f)

/-- A relation between source-chart points lifts to the actual restricted relation scheme. -/
theorem translatedRestricted_point_lift (x y : (translatedSourceIntersection f hL i).left)
    (a : (smoothHilbertRelation f hL).left)
    (ha : (smoothHilbertRelationFst f hL).left a = (translatedSourceInclusion f hL i).left x)
    (hb : (smoothHilbertRelationSnd f hL).left a = (translatedSourceInclusion f hL i).left y) :
    ∃ z : (translatedRestrictedRelation f hL i).left,
      (translatedRestrictedFst f hL i).left z = x ∧
        (translatedRestrictedSnd f hL i).left z = y := by
  have H₁ := (IsPullback.of_hasPullback
    (smoothHilbertRelationFst f hL) (translatedSourceInclusion f hL i)).map (Over.forget _)
  obtain ⟨b, hb₁, hb₂⟩ := Scheme.exists_preimage_of_isPullback H₁ a x ha
  have he : (translatedRelationOther f hL i).left b =
      (translatedSourceInclusion f hL i).left y := by
    exact (congrArg (smoothHilbertRelationSnd f hL).left hb₁).trans hb
  have H₂ := (IsPullback.of_hasPullback
    (translatedRelationOther f hL i) (translatedSourceInclusion f hL i)).map (Over.forget _)
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.exists_preimage_of_isPullback H₂ b y he
  refine ⟨z, ?_, hz₂⟩
  exact (congrArg (pullback.snd (smoothHilbertRelationFst f hL)
    (translatedSourceInclusion f hL i)).left hz₁).trans hb₂

/-- The original orbit relation is exactly equality of actual chart parameters. -/
theorem translatedSource_related_iff (x y : (translatedSourceIntersection f hL i).left) :
    Related (smoothHilbertRelationFst f hL) (smoothHilbertRelationSnd f hL)
      ((translatedSourceInclusion f hL i).left x) ((translatedSourceInclusion f hL i).left y) ↔
    (translatedSourceParameter f hL i).left x = (translatedSourceParameter f hL i).left y := by
  constructor
  · rintro ⟨a, ha, hb⟩
    obtain ⟨z, hx, hy⟩ := translatedRestricted_point_lift f hL i x y a ha hb
    have h := congrArg (fun k ↦ k.left z) (translatedRestricted_condition f hL i)
    change (translatedSourceParameter f hL i).left ((translatedRestrictedFst f hL i).left z) =
      (translatedSourceParameter f hL i).left ((translatedRestrictedSnd f hL i).left z) at h
    rwa [hx, hy] at h
  · intro h
    have H := (translatedRestricted_isPullback f hL i).map (Over.forget _)
    obtain ⟨z, hx, hy⟩ := Scheme.exists_preimage_of_isPullback H x y h
    refine ⟨(translatedRestrictedToRelation f hL i).left z, ?_, ?_⟩
    · exact (congrArg (fun k ↦ k.left z) (translatedRestrictedToRelation_fst f hL i)).trans
        (congrArg (translatedSourceInclusion f hL i).left hx)
    · exact (congrArg (fun k ↦ k.left z) (translatedRestrictedToRelation_snd f hL i)).trans
        (congrArg (translatedSourceInclusion f hL i).left hy)

/-- The two surjections from the source chart have precisely the same fibers. -/
theorem translatedSourceOrbitMap_eq_iff (x y : (translatedSourceIntersection f hL i).left) :
    translatedSourceOrbitMap f hL i x = translatedSourceOrbitMap f hL i y ↔
      (translatedSourceParameter f hL i).left x = (translatedSourceParameter f hL i).left y := by
  rw [Subtype.ext_iff]
  exact (projection_eq_iff (smoothHilbertEquivalenceRelation f hL) _ _).trans
    (translatedSource_related_iff f hL i x y)

end FLT.Mazur.HilbertChart
