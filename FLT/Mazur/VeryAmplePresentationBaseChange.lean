/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeVeryAmpleLineBundle

/-!
# Closed projective presentations under affine base change

Both the closed immersion and its hyperplane sheaf are pulled back along an
arbitrary coefficient ring map, without flatness or reducedness assumptions.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProjectiveSpace.VeryAmplePresentation
variable {A B : Type} [CommRing A] [CommRing B] {X : Scheme}
  {f : X ⟶ Spec (.of A)} {L : X.Modules} (p : VeryAmplePresentation f L) (φ : A →+* B)

/-- The base-changed presentation map into projective space over the new ring. -/
def baseChangeEmbedding :
    pullback f (Spec.map (CommRingCat.ofHom φ)) ⟶ space B (Fin (p.dimension + 1)) :=
  coefficientLift φ (pullback.fst f (Spec.map (CommRingCat.ofHom φ)) ≫ p.embedding)
    (pullback.snd f (Spec.map (CommRingCat.ofHom φ)))
    (by rw [Category.assoc, p.over, pullback.condition])

/-- The projective embedding square is the actual scheme pullback square. -/
theorem baseChangeEmbedding_isPullback :
    IsPullback (p.baseChangeEmbedding φ) (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))
      (coefficientMap φ _) p.embedding := by
  apply IsPullback.of_right (h₁₂ := baseProjection B _) (h₂₂ := baseProjection A _)
  · simpa only [baseChangeEmbedding, coefficientLift_baseProjection, p.over] using
      (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom φ))).flip
  · exact coefficientLift_comp _ _ _ _
  · exact (coefficient_isPullback φ p.dimension).flip

/-- Base change preserves the closed immersion of the actual presentation. -/
instance baseChangeEmbedding_isClosedImmersion : IsClosedImmersion (p.baseChangeEmbedding φ) :=
  MorphismProperty.of_isPullback (p.baseChangeEmbedding_isPullback φ).flip inferInstance

/-- Base change of an actual projective presentation, including its line-bundle coefficients. -/
def baseChange : VeryAmplePresentation (pullback.snd f (Spec.map (CommRingCat.ofHom φ)))
    ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).obj L) where
  dimension := p.dimension
  embedding := p.baseChangeEmbedding φ
  isClosedImmersion := inferInstance
  over := coefficientLift_baseProjection _ _ _ _
  coefficientIso :=
    (Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).mapIso
      p.coefficientIso ≪≫
      (Scheme.Modules.pullbackComp _ _).app _ ≪≫ coefficientLiftTwistingIso φ _ _ _ 1

/-- The construction retains the original projective dimension. -/
@[simp]
lemma baseChange_dimension : (p.baseChange φ).dimension = p.dimension := rfl

/-- The constructed embedding reduces to the original embedding by the coefficient map. -/
@[reassoc (attr := simp)]
lemma baseChange_embedding_comp :
    (p.baseChange φ).embedding ≫ coefficientMap φ (Fin (p.dimension + 1)) =
    pullback.fst f (Spec.map (CommRingCat.ofHom φ)) ≫ p.embedding :=
  coefficientLift_comp _ _ _ _

end FLT.Mazur.ProjectiveSpace.VeryAmplePresentation
