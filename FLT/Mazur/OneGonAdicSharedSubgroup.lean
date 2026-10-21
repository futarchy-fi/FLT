/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicSharedStage
public import FLT.Mazur.OneGonAdicIndependentSubgroupRefinement
public import FLT.Mazur.OneGonAdicIndependentSubgroupRecovery

/-!
# Actual supplied subgroups refined into a shared finite ring

The shared subgroup uses the transition of the supplied smooth factor. It
retains the full embedding, rank and group law, together with actual recovery.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicIndependentModel
open Approximation OneGonAdicCharacterTower OneGonSmoothing CharacterSchemeBaseChange
open ArithmeticOneGonGeneralizedCurve WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s : Set R)
  (K : Subalgebra ℤ R) [Algebra.FiniteType ℤ K]
  (hS : base I t ht n s ≤ K)

variable (i : (CoefficientStage (base I t ht n s))ᵒᵖ)
  (hi : stageBase I t ht n s i ≤ K)
  (b : (coefficientModelDiagram (base I t ht n s) (carrier I t ht n s).hom).obj i ⟶
    (integralSmoothOpen (equation (parameter I t ht n s))).toScheme)
  (hb : b ≫ (integralSmoothOpen (equation (parameter I t ht n s))).ι =
    (coefficientModelToInitial (base I t ht n s) (carrier I t ht n s).hom).app i ≫
      embedding I t ht n s)
  (hs : complementaryInverse I t ht ∈ s)
  (hφ : Function.Surjective (OneGonFiniteCoefficientCoordinates.modelCoordinates t 1
    (canonicalCoordinates I t ht n) s))

/-- Refine the supplied smooth factor along the actual shared-stage transition. -/
def sharedFiniteSubgroup :
    GeneralizedEllipticCurve.FiniteSubgroup (S := Spec (.of K))
      (stageCurve I t ht n s (sharedStage I t ht n s K hS) hs) n :=
  refinedFiniteSubgroup I t ht n s (sharedToStage I t ht n s K hS i hi) b hb hs hφ

/-- The full embedding of the refined supplied subgroup is the intrinsic shared embedding. -/
theorem sharedFiniteSubgroup_curveMap :
    (sharedFiniteSubgroup I t ht n s K hS i hi b hb hs hφ).curveMap =
      (stageCharacterIso I t ht n s (sharedStage I t ht n s K hS)).hom ≫
        stageEmbedding I t ht n s (sharedStage I t ht n s K hS) hs :=
  stageFiniteSubgroup_curveMap I t ht n s (sharedStage I t ht n s K hS)
    (refinedFactor I t ht n s (sharedToStage I t ht n s K hS i hi) b)
    (refinedFactor_inclusion I t ht n s (sharedToStage I t ht n s K hS i hi) b hb) hs hφ

/-- The shared subgroup recovers the actual original subgroup, including its source group. -/
def sharedFiniteSubgroupRecoveryIso :=
  stageFiniteSubgroupRecoveryIso I t ht n s (sharedStage I t ht n s K hS)
    (refinedFactor I t ht n s (sharedToStage I t ht n s K hS i hi) b)
    (refinedFactor_inclusion I t ht n s (sharedToStage I t ht n s K hS i hi) b hb) hs hφ

/-- All infinitesimal multiplicities in the shared subgroup ideal are retained. -/
theorem sharedFiniteSubgroup_ideal :
    (sharedFiniteSubgroup I t ht n s K hS i hi b hb hs hφ).ideal =
      (stageEmbedding I t ht n s (sharedStage I t ht n s K hS) hs).left.ker :=
  stageFiniteSubgroup_ideal I t ht n s (sharedStage I t ht n s K hS)
    (refinedFactor I t ht n s (sharedToStage I t ht n s K hS i hi) b)
    (refinedFactor_inclusion I t ht n s (sharedToStage I t ht n s K hS i hi) b hb) hs hφ

end FLT.Mazur.OneGonAdicIndependentModel
