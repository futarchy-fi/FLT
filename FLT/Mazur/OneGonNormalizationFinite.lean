/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonNormalizationPullback
public import FLT.Mazur.PolygonNormalizationAlgebra
/-!
# Finite surjective normalization of the one-gon

The computed inverse images of the node and torus charts reduce finiteness
to the integral affine normalization and the identity on the torus. This
proves the property for the existing global normalization morphism.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace FLT.Mazur.OneGonNormalizationFinite
open OneGonNormalization OneGonNormalizationPullback PinchingAffineDescent
variable (K : Type u) [Field K]

instance affine_finite : IsFinite (oneBranch K) :=
  PolygonNormalizationAlgebra.oneGon_spec_finite

/-- The pinched chart and the entire torus cover the one-gon. -/
def targetCover : (OneGonGluing.scheme K).OpenCover :=
  BinaryOpenDescent.cover (OneGonGluing.node K) (OneGonGluing.torus K)
    (OneGonGluing.charts_cover K)

/-- The specified projective normalization morphism is finite. -/
instance normalization_finite : IsFinite (normalization K) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsFinite) (targetCover K)
  intro b
  cases b
  · change IsFinite (pullback.snd (normalization K) (OneGonGluing.node K))
    rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite)
      (node_isPullback K).flip.isoPullback.hom,
      (node_isPullback K).flip.isoPullback_hom_snd]
    infer_instance
  · change IsFinite (pullback.snd (normalization K) (OneGonGluing.torus K))
    rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite)
      (torus_isPullback K).flip.isoPullback.hom,
      (torus_isPullback K).flip.isoPullback_hom_snd]
    infer_instance

/-- Every point lifts to the specified projective normalization. -/
theorem normalization_surjective : Function.Surjective (normalization K) := by
  intro x
  rcases OneGonGluing.charts_cover K x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · obtain ⟨z, hz⟩ := PolygonNormalizationAlgebra.oneGon_comap_surjective y
    refine ⟨OneGonAffineNormalization.alpha K z, ?_⟩
    change (OneGonAffineNormalization.alpha K ≫ normalization K) z = _
    rw [OneGonAffineNormalization.alpha_normalization]
    exact congrArg (OneGonGluing.node K) hz
  · exact ⟨torusLift K y, congrArg (fun f ↦ f y) (torus_normalization K)⟩
end FLT.Mazur.OneGonNormalizationFinite
