/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicSharedRecovery
public import FLT.Mazur.OneGonCommonSubgroupRecovery

/-!
# Entire subgroup embedding squares over any shared finite ring

Injectivity of the shared subalgebra in the ambient adic ring detects the
recovered square. Thus the full embedding square already holds over the finite ring.
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
  (K : Subalgebra ℤ R) [Algebra.FiniteType ℤ K]
  (hS : base I t ht n s ≤ K) (hU : base I t ht n u ≤ K)
  (hs : complementaryInverse I t ht ∈ s) (hu : complementaryInverse I t ht ∈ u)

/-- Entire intrinsic character embeddings agree over the finite common ring itself. -/
theorem shared_intrinsic_embedding_square :
    ((stageCharacterIso I t ht n s (sharedStage I t ht n s K hS)).hom ≫
      stageEmbedding I t ht n s (sharedStage I t ht n s K hS) hs) ≫
        (sharedCurveIso I t ht n s u K hS hU hs hu).hom.curve =
    (stageCharacterIso I t ht n u (sharedStage I t ht n u K hU)).hom ≫
      stageEmbedding I t ht n u (sharedStage I t ht n u K hU) hu := by
  let _ : IsSeparated (curve I t ht n u hu).curve.hom :=
    inferInstanceAs (IsSeparated (integralCurveStructure (equation (parameter I t ht n u))))
  let _ : IsSeparated (stageCurve I t ht n u (sharedStage I t ht n u K hU) hu).curve.hom :=
    MorphismProperty.pullback_snd _ _ inferInstance
  apply pullback_map_injective K R (ZMod n)
    (show Function.Injective (algebraMap K R) from
      Subtype.val_injective)
    (stageCurve I t ht n u (sharedStage I t ht n u K hU) hu).curve
  exact (cancel_epi (overIso K R (ZMod n)).hom).mp
    (shared_embedding_recovery I t ht n s u K hS hU hs hu)

end FLT.Mazur.OneGonAdicIndependentModel
