/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicIndependentSourceTower
public import FLT.Mazur.ArithmeticOneGonCoefficientTower

/-!
# Tower coherence for arbitrary independent stages

The full generalized-curve recovery agrees with successive
coefficient changes along the supplied stage inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicIndependentModel
open OneGonAdicCharacterTower Approximation
open OneGonSmoothing CharacterSchemeBaseChange GeneralizedEllipticCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s : Set R)
  (i : (CoefficientStage (base I t ht n s))ᵒᵖ)
  (hi : complementaryInverse I t ht ∈ s)

/-- The full arithmetic recovery is the successive comparison through the actual stage. -/
theorem stageGeneralizedRecoveryIso_tower :
    (stageGeneralizedRecoveryIso I t ht n s i hi).hom =
      (ArithmeticOneGonGeneralizedCurve.iteratedCoefficientIso
        (base I t ht n s) (stageBase I t ht n s i) R (parameter I t ht n s)
        (parameter_complementaryUnit I t ht n s hi)).hom := by
  rw [stageGeneralizedRecoveryIso_def]
  exact (ArithmeticOneGonGeneralizedCurve.coefficientIso_tower
    (base I t ht n s) (stageBase I t ht n s i) R (parameter I t ht n s)
    (parameter_complementaryUnit I t ht n s hi)).symm

/-- Intrinsic stage characters recover the whole embedding without an extra equality premise. -/
theorem stage_intrinsic_embedding_recovery :
    (overIso (stageBase I t ht n s i) R (ZMod n)).hom ≫
      (Over.pullback (baseMap (stageBase I t ht n s i) R)).map
        ((stageCharacterIso I t ht n s i).hom ≫ stageEmbedding I t ht n s i hi) =
      (canonicalFiniteSubgroup I t ht n).curveMap ≫
        (stageGeneralizedRecoveryIso I t ht n s i hi).hom.curve := by
  rw [Functor.map_comp, ← Category.assoc, ← stageFullSourceIso_tower]
  exact stage_full_embedding_recovery I t ht n s i hi

end FLT.Mazur.OneGonAdicIndependentModel
