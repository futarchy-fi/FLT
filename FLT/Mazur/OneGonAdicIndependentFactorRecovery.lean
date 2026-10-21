/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicIndependentFactorClosed

/-!
# Recovery of arbitrary intrinsic smooth factors

The full generalized-curve recovery and whole-embedding equation force the
smooth-factor recovery by cancellation of the actual smooth inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicIndependentModel
open Approximation OneGonAdicCharacterTower OneGonSmoothing CharacterSchemeBaseChange
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s : Set R)
  (i : (CoefficientStage (base I t ht n s))ᵒᵖ)
  (b : (coefficientModelDiagram (base I t ht n s) (carrier I t ht n s).hom).obj i ⟶
    (integralSmoothOpen (equation (parameter I t ht n s))).toScheme)
  (hb : b ≫ (integralSmoothOpen (equation (parameter I t ht n s))).ι =
    (coefficientModelToInitial (base I t ht n s) (carrier I t ht n s).hom).app i ≫
      embedding I t ht n s)
  (hi : complementaryInverse I t ht ∈ s)

/-- Recovery identifies the actual smooth map with the complete-base subgroup inclusion. -/
theorem stageCharacterFactor_recovery :
    (overIso (stageBase I t ht n s i) R (ZMod n)).hom ≫
      (Over.pullback (baseMap (stageBase I t ht n s i) R)).map
        (stageCharacterFactor I t ht n s i b hb hi) =
      (canonicalFiniteSubgroup I t ht n).inclusion ≫
        (stageGeneralizedRecoveryIso I t ht n s i hi).hom.group := by
  let _ : Mono ((stageCurve I t ht n s i hi).baseChange
      (baseMap (stageBase I t ht n s i) R)).inclusion := by
    dsimp [GeneralizedEllipticCurve.inclusion, curveSmoothInclusion]
    infer_instance
  apply (cancel_mono ((stageCurve I t ht n s i hi).baseChange
    (baseMap (stageBase I t ht n s i) R)).inclusion).mp
  rw [Category.assoc, Category.assoc,
    ← (stageGeneralizedRecoveryIso I t ht n s i hi).hom.inclusion,
    GeneralizedEllipticCurve.baseChange_inclusion]
  change (overIso (stageBase I t ht n s i) R (ZMod n)).hom ≫
      ((Over.pullback (baseMap (stageBase I t ht n s i) R)).map
        (stageCharacterFactor I t ht n s i b hb hi) ≫
      (Over.pullback (baseMap (stageBase I t ht n s i) R)).map
        (stageCurve I t ht n s i hi).inclusion) = _
  rw [← Functor.map_comp, stageCharacterFactor_inclusion]
  exact (stage_intrinsic_embedding_recovery I t ht n s i hi).trans (Category.assoc _ _ _)

end FLT.Mazur.OneGonAdicIndependentModel
