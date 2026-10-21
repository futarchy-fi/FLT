/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicIndependentCommonRecovery
public import FLT.Mazur.OneGonCommonSubgroupRecovery

/-!
# Descending independent whole embeddings to the finite common ring

The common subalgebra embeds in the original ring. Separated-target detection
therefore descends the constructed recovered equality of entire embeddings.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicIndependentModel
open Approximation OneGonAdicCharacterTower OneGonSmoothing CharacterSchemeBaseChange
open ArithmeticOneGonGeneralizedCurve WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s u : Set R)
  (i : (CoefficientStage (base I t ht n s))ᵒᵖ)
  (j : (CoefficientStage (base I t ht n u))ᵒᵖ)
  (hs : complementaryInverse I t ht ∈ s) (hu : complementaryInverse I t ht ∈ u)

/-- Entire intrinsic character embeddings agree over the finite common ring itself. -/
theorem common_intrinsic_embedding_square :
    ((stageCharacterIso I t ht n s (commonLeft I t ht n s u i j)).hom ≫
      stageEmbedding I t ht n s (commonLeft I t ht n s u i j) hs) ≫
        (commonCurveIso I t ht n s u i j hs hu).hom.curve =
    (stageCharacterIso I t ht n u (commonRight I t ht n s u i j)).hom ≫
      stageEmbedding I t ht n u (commonRight I t ht n s u i j) hu := by
  let _ : IsSeparated (curve I t ht n u hu).curve.hom :=
    inferInstanceAs (IsSeparated (integralCurveStructure (equation (parameter I t ht n u))))
  let _ : IsSeparated (stageCurve I t ht n u (commonRight I t ht n s u i j) hu).curve.hom :=
    MorphismProperty.pullback_snd _ _ inferInstance
  apply pullback_map_injective (commonBase I t ht n s u i j) R (ZMod n)
    (show Function.Injective (algebraMap (commonBase I t ht n s u i j) R) from
      Subtype.val_injective)
    (stageCurve I t ht n u (commonRight I t ht n s u i j) hu).curve
  exact (cancel_epi (overIso (commonBase I t ht n s u i j) R (ZMod n)).hom).mp
    (common_embedding_recovery I t ht n s u i j hs hu)

end FLT.Mazur.OneGonAdicIndependentModel
