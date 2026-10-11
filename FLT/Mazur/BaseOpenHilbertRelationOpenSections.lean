/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseOpenHilbertChartSourceSections

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
  (d : ℕ) (T₀ : Over (Spec (.of R))) [IsOpenImmersion T₀.hom]
  (c : (relativeFppfSheaf f).obj.obj (op T₀))

/-- The first restriction of the original relation is an open immersion. -/
instance baseOpenRelationFirst_isOpenImmersion :
    IsOpenImmersion (pullback.fst (smoothHilbertRelationFst f hL)
      (variableSourceInclusion f hL d T₀ c)).left :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback (smoothHilbertRelationFst f hL)
      (variableSourceInclusion f hL d T₀ c)).map (Over.forget _)).flip
      (inferInstanceAs (IsOpenImmersion (variableSourceInclusion f hL d T₀ c).left))

/-- The second endpoint restriction is also an actual open immersion. -/
instance baseOpenRelationSecond_isOpenImmersion :
    IsOpenImmersion (pullback.fst (baseOpenRelationOther f hL d T₀ c)
      (variableSourceInclusion f hL d T₀ c)).left :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback (baseOpenRelationOther f hL d T₀ c)
      (variableSourceInclusion f hL d T₀ c)).map (Over.forget _)).flip
      (inferInstanceAs (IsOpenImmersion (variableSourceInclusion f hL d T₀ c).left))

/-- The restricted relation is an open subscheme of the original relation. -/
instance baseOpenRestrictedToRelation_isOpenImmersion :
    IsOpenImmersion (baseOpenRestrictedToRelation f hL d T₀ c).left :=
  inferInstanceAs (IsOpenImmersion
    ((pullback.fst (baseOpenRelationOther f hL d T₀ c)
      (variableSourceInclusion f hL d T₀ c)).left ≫
      (pullback.fst (smoothHilbertRelationFst f hL)
        (variableSourceInclusion f hL d T₀ c)).left))

/-- Original arrows whose first endpoint lies in the chart lift retaining that arrow. -/
theorem baseOpenRestricted_original_lift (r : (smoothHilbertRelation f hL).left)
    (x : (variableSourceIntersection f hL d T₀ c).left)
    (hx : (smoothHilbertRelationFst f hL).left r =
      (variableSourceInclusion f hL d T₀ c).left x) :
    ∃ z : (baseOpenRestrictedRelation f hL d T₀ c).left,
      (baseOpenRestrictedToRelation f hL d T₀ c).left z = r ∧
        (baseOpenRestrictedFst f hL d T₀ c).left z = x := by
  have hr : (smoothHilbertRelationFst f hL).left r ∈ baseOpenSourceOpen f hL d T₀ c :=
    hx ▸ ⟨x, rfl⟩
  have hr' : (smoothHilbertRelationSnd f hL).left r ∈ baseOpenSourceOpen f hL d T₀ c :=
    (Set.ext_iff.mp (congrArg SetLike.coe (baseOpenSourceOpen_invariant f hL d T₀ c)) r).mp hr
  obtain ⟨y, hy⟩ := hr'
  have H₁ := (IsPullback.of_hasPullback
    (smoothHilbertRelationFst f hL) (variableSourceInclusion f hL d T₀ c)).map (Over.forget _)
  obtain ⟨b, hb₁, hb₂⟩ := Scheme.exists_preimage_of_isPullback H₁ r x hx
  have he : (baseOpenRelationOther f hL d T₀ c).left b =
      (variableSourceInclusion f hL d T₀ c).left y :=
    (congrArg (smoothHilbertRelationSnd f hL).left hb₁).trans hy.symm
  have H₂ := (IsPullback.of_hasPullback
    (baseOpenRelationOther f hL d T₀ c) (variableSourceInclusion f hL d T₀ c)).map (Over.forget _)
  obtain ⟨z, hz₁, _⟩ := Scheme.exists_preimage_of_isPullback H₂ b y he
  exact ⟨z,
    (congrArg (pullback.fst (smoothHilbertRelationFst f hL)
      (variableSourceInclusion f hL d T₀ c)).left hz₁).trans hb₁,
    (congrArg (pullback.snd (smoothHilbertRelationFst f hL)
      (variableSourceInclusion f hL d T₀ c)).left hz₁).trans hb₂⟩

/-- Every first-endpoint subopen is exactly its image in the original relation. -/
theorem baseOpenRestricted_image_fst (V : (variableSourceIntersection f hL d T₀ c).left.Opens) :
    (baseOpenRestrictedToRelation f hL d T₀ c).left ''ᵁ
      ((baseOpenRestrictedFst f hL d T₀ c).left ⁻¹ᵁ V) =
    (smoothHilbertRelationFst f hL).left ⁻¹ᵁ
      ((variableSourceInclusion f hL d T₀ c).left ''ᵁ V) := by
  ext r
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(baseOpenRestrictedFst f hL d T₀ c).left z, hz, ?_⟩
    exact (congrArg (fun k ↦ k.left z) (baseOpenRestrictedToRelation_fst f hL d T₀ c)).symm
  · rintro ⟨x, hx, he⟩
    obtain ⟨z, hz, hzx⟩ := baseOpenRestricted_original_lift f hL d T₀ c r x he.symm
    refine ⟨z, ?_, hz⟩
    change (baseOpenRestrictedFst f hL d T₀ c).left z ∈ V
    rwa [hzx]

/-- All restricted relation functions are the actual original relation-open functions. -/
def baseOpenRestrictedSectionsIso (V : (variableSourceIntersection f hL d T₀ c).left.Opens) :
    Γ((smoothHilbertRelation f hL).left,
      (smoothHilbertRelationFst f hL).left ⁻¹ᵁ
        ((variableSourceInclusion f hL d T₀ c).left ''ᵁ V)) ≅
    Γ((baseOpenRestrictedRelation f hL d T₀ c).left,
      (baseOpenRestrictedFst f hL d T₀ c).left ⁻¹ᵁ V) :=
  (smoothHilbertRelation f hL).left.presheaf.mapIso
    (eqToIso (congrArg op (baseOpenRestricted_image_fst f hL d T₀ c V).symm)) ≪≫
      (baseOpenRestrictedToRelation f hL d T₀ c).left.appIso _

end FLT.Mazur.HilbertChart
