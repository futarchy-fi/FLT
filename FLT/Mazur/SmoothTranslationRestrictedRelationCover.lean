/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertRelationBridge
public import FLT.Mazur.SmoothTranslationOrbitOpen

/-!
# Smooth covers of the original invariant source and relation opens

The common source covers its actual open image. Its full restricted relation
covers precisely the original relation above that invariant image. Both
covering assertions use actual scheme pullbacks, including residue extensions.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Restricting a scheme map to an open contained in its image makes it surjective. -/
theorem surjective_morphismRestrict_of_range {Y Z : Scheme} (g : Y ⟶ Z) (W : Z.Opens)
    (hW : (W : Set Z) ⊆ Set.range g) : Surjective (g ∣_ W) := by
  constructor
  rintro ⟨z, hz⟩
  obtain ⟨y, hy⟩ := hW hz
  refine ⟨⟨y, ?_⟩, ?_⟩
  · change g y ∈ W
    rwa [hy]
  · apply Subtype.ext
    exact (morphismRestrict_base_coe g W _).trans hy

variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Smooth V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))

instance smoothTranslationRestrictedToRelation_smooth :
    Smooth (baseOpenRestrictedToRelation f hL d V c).left := by
  let _ : Smooth (pullback.fst (smoothHilbertRelationFst f hL)
      (variableSourceInclusion f hL d V c)).left :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback _ _).map (Over.forget _)).flip
      (inferInstanceAs (Smooth (variableSourceInclusion f hL d V c).left))
  let _ : Smooth (pullback.fst (baseOpenRelationOther f hL d V c)
      (variableSourceInclusion f hL d V c)).left :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback _ _).map (Over.forget _)).flip
      (inferInstanceAs (Smooth (variableSourceInclusion f hL d V c).left))
  dsimp only [baseOpenRestrictedToRelation, Over.comp_left]
  infer_instance

/-- The restricted relation's image is exactly the original relation over the source image. -/
theorem smoothTranslationRestrictedToRelation_range :
    Set.range (baseOpenRestrictedToRelation f hL d V c).left =
      ((smoothHilbertRelationFst f hL).left ⁻¹ᵁ
        smoothTranslationSourceOpen f hL d V c : Set _) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(baseOpenRestrictedFst f hL d V c).left x,
      (congrArg (fun k ↦ k.left x) (baseOpenRestrictedToRelation_fst f hL d V c)).symm⟩
  · intro hz
    have hz' : z ∈ (smoothHilbertRelationSnd f hL).left ⁻¹ᵁ
        smoothTranslationSourceOpen f hL d V c := by
      rwa [← smoothTranslationSourceOpen_invariant]
    obtain ⟨x, hx⟩ := hz
    obtain ⟨y, hy⟩ := hz'
    have H₁ := (IsPullback.of_hasPullback (smoothHilbertRelationFst f hL)
      (variableSourceInclusion f hL d V c)).map (Over.forget _)
    obtain ⟨u, hu, _⟩ := Scheme.exists_preimage_of_isPullback H₁ z x hx.symm
    have he : (baseOpenRelationOther f hL d V c).left u =
        (variableSourceInclusion f hL d V c).left y :=
      (congrArg (smoothHilbertRelationSnd f hL).left hu).trans hy.symm
    have H₂ := (IsPullback.of_hasPullback (baseOpenRelationOther f hL d V c)
      (variableSourceInclusion f hL d V c)).map (Over.forget _)
    obtain ⟨v, hv, _⟩ := Scheme.exists_preimage_of_isPullback H₂ u y he
    exact ⟨v, (congrArg (pullback.fst (smoothHilbertRelationFst f hL)
      (variableSourceInclusion f hL d V c)).left hv).trans hu⟩

/-- Every open inside the actual source image has a proved smooth surjective source cover. -/
theorem smoothTranslationSourceRestriction_surjective
    (W : (smoothHilbertSource f).left.Opens) (hW : W ≤ smoothTranslationSourceOpen f hL d V c) :
    Surjective ((variableSourceInclusion f hL d V c).left ∣_ W) :=
  surjective_morphismRestrict_of_range _ W hW

/-- Every relation open above the source image has a proved surjective restricted relation cover. -/
theorem smoothTranslationRelationRestriction_surjective
    (W : (smoothHilbertSource f).left.Opens) (hW : W ≤ smoothTranslationSourceOpen f hL d V c) :
    Surjective ((baseOpenRestrictedToRelation f hL d V c).left ∣_
      ((smoothHilbertRelationFst f hL).left ⁻¹ᵁ W)) := by
  apply surjective_morphismRestrict_of_range
  rw [smoothTranslationRestrictedToRelation_range]
  exact fun _ hx ↦ hW hx

end FLT.Mazur.HilbertChart
