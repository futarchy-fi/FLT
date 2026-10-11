/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertChartSourceSections

/-!
# The restricted kernel pair as an actual original relation open

Invariance of the source chart makes the two-endpoint relation restriction
an open subscheme with exactly the expected first-endpoint image. This
identifies the relation function domains needed for invariant-sheaf comparison.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (i : TranslatedHilbertIndex f)

/-- The first restriction of the original relation is an open immersion. -/
instance translatedRelationFirst_isOpenImmersion :
    IsOpenImmersion (pullback.fst (smoothHilbertRelationFst f hL)
      (translatedSourceInclusion f hL i)).left :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback (smoothHilbertRelationFst f hL)
      (translatedSourceInclusion f hL i)).map (Over.forget _)).flip
      (inferInstanceAs (IsOpenImmersion (translatedSourceInclusion f hL i).left))

/-- The second endpoint restriction is also an actual open immersion. -/
instance translatedRelationSecond_isOpenImmersion :
    IsOpenImmersion (pullback.fst (translatedRelationOther f hL i)
      (translatedSourceInclusion f hL i)).left :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback (translatedRelationOther f hL i)
      (translatedSourceInclusion f hL i)).map (Over.forget _)).flip
      (inferInstanceAs (IsOpenImmersion (translatedSourceInclusion f hL i).left))

/-- The restricted relation is an open subscheme of the original relation. -/
instance translatedRestrictedToRelation_isOpenImmersion :
    IsOpenImmersion (translatedRestrictedToRelation f hL i).left :=
  inferInstanceAs (IsOpenImmersion
    ((pullback.fst (translatedRelationOther f hL i)
      (translatedSourceInclusion f hL i)).left ≫
      (pullback.fst (smoothHilbertRelationFst f hL)
        (translatedSourceInclusion f hL i)).left))

/-- Original arrows whose first endpoint lies in the chart lift retaining that arrow. -/
theorem translatedRestricted_original_lift (r : (smoothHilbertRelation f hL).left)
    (x : (translatedSourceIntersection f hL i).left)
    (hx : (smoothHilbertRelationFst f hL).left r =
      (translatedSourceInclusion f hL i).left x) :
    ∃ z : (translatedRestrictedRelation f hL i).left,
      (translatedRestrictedToRelation f hL i).left z = r ∧
        (translatedRestrictedFst f hL i).left z = x := by
  have hr : (smoothHilbertRelationFst f hL).left r ∈ translatedSourceOpen f hL i :=
    hx ▸ ⟨x, rfl⟩
  have hr' : (smoothHilbertRelationSnd f hL).left r ∈ translatedSourceOpen f hL i :=
    (Set.ext_iff.mp (congrArg SetLike.coe (translatedSourceOpen_invariant f hL i)) r).mp hr
  obtain ⟨y, hy⟩ := hr'
  have H₁ := (IsPullback.of_hasPullback
    (smoothHilbertRelationFst f hL) (translatedSourceInclusion f hL i)).map (Over.forget _)
  obtain ⟨b, hb₁, hb₂⟩ := Scheme.exists_preimage_of_isPullback H₁ r x hx
  have he : (translatedRelationOther f hL i).left b =
      (translatedSourceInclusion f hL i).left y :=
    (congrArg (smoothHilbertRelationSnd f hL).left hb₁).trans hy.symm
  have H₂ := (IsPullback.of_hasPullback
    (translatedRelationOther f hL i) (translatedSourceInclusion f hL i)).map (Over.forget _)
  obtain ⟨z, hz₁, _⟩ := Scheme.exists_preimage_of_isPullback H₂ b y he
  exact ⟨z,
    (congrArg (pullback.fst (smoothHilbertRelationFst f hL)
      (translatedSourceInclusion f hL i)).left hz₁).trans hb₁,
    (congrArg (pullback.snd (smoothHilbertRelationFst f hL)
      (translatedSourceInclusion f hL i)).left hz₁).trans hb₂⟩

/-- Every first-endpoint subopen is exactly its image in the original relation. -/
theorem translatedRestricted_image_fst (V : (translatedSourceIntersection f hL i).left.Opens) :
    (translatedRestrictedToRelation f hL i).left ''ᵁ
      ((translatedRestrictedFst f hL i).left ⁻¹ᵁ V) =
    (smoothHilbertRelationFst f hL).left ⁻¹ᵁ
      ((translatedSourceInclusion f hL i).left ''ᵁ V) := by
  ext r
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(translatedRestrictedFst f hL i).left z, hz, ?_⟩
    exact (congrArg (fun k ↦ k.left z) (translatedRestrictedToRelation_fst f hL i)).symm
  · rintro ⟨x, hx, he⟩
    obtain ⟨z, hz, hzx⟩ := translatedRestricted_original_lift f hL i r x he.symm
    refine ⟨z, ?_, hz⟩
    change (translatedRestrictedFst f hL i).left z ∈ V
    rwa [hzx]

/-- All restricted relation functions are the actual original relation-open functions. -/
def translatedRestrictedSectionsIso (V : (translatedSourceIntersection f hL i).left.Opens) :
    Γ((smoothHilbertRelation f hL).left,
      (smoothHilbertRelationFst f hL).left ⁻¹ᵁ
        ((translatedSourceInclusion f hL i).left ''ᵁ V)) ≅
    Γ((translatedRestrictedRelation f hL i).left,
      (translatedRestrictedFst f hL i).left ⁻¹ᵁ V) :=
  (smoothHilbertRelation f hL).left.presheaf.mapIso
    (eqToIso (congrArg op (translatedRestricted_image_fst f hL i V).symm)) ≪≫
      (translatedRestrictedToRelation f hL i).left.appIso _

end FLT.Mazur.HilbertChart
