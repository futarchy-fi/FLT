/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicIndependentFactorHom

/-!
# Finite subgroups at arbitrary independent smooth stages

Every supplied smooth factor with surjective support coordinates gives a
rank-n closed subgroup on the intrinsic character source. Its whole ideal
retains the original stage embedding and recovers the canonical full ideal.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped CategoryTheory.Obj
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

variable (hφ : Function.Surjective (OneGonFiniteCoefficientCoordinates.modelCoordinates t 1
  (canonicalCoordinates I t ht n) s))

/-- The supplied stage with its proved closed homomorphism and intrinsic rank-n source. -/
def stageFiniteSubgroup : (stageCurve I t ht n s i hi).FiniteSubgroup n where
  carrier := model (stageBase I t ht n s i) (ZMod n)
  commGroup := RootsOfUnityScheme.commGrpObj (stageBase I t ht n s i) n
  inclusion := stageCharacterFactor I t ht n s i b hb hi
  closed := stageCharacterFactor_isClosedImmersion I t ht n s i b hb hi hφ
  degree := RootsOfUnityScheme.degree (stageBase I t ht n s i) n

/-- The whole-curve map uses the actual stage embedding and character identification. -/
theorem stageFiniteSubgroup_curveMap :
    (stageFiniteSubgroup I t ht n s i b hb hi hφ).curveMap =
      (stageCharacterIso I t ht n s i).hom ≫ stageEmbedding I t ht n s i hi :=
  stageCharacterFactor_inclusion I t ht n s i b hb hi

/-- Passing to the intrinsic character source preserves the entire stage ideal. -/
theorem stageFiniteSubgroup_ideal :
    (stageFiniteSubgroup I t ht n s i b hb hi hφ).ideal =
      (stageEmbedding I t ht n s i hi).left.ker := by
  change (stageFiniteSubgroup I t ht n s i b hb hi hφ).curveMap.left.ker = _
  rw [stageFiniteSubgroup_curveMap, Over.comp_left, Scheme.Hom.ker_comp_of_isIso]

/-- The bundled subgroup recovers the canonical ideal with all infinitesimal multiplicities. -/
theorem stageFiniteSubgroup_recovery_ideal :
    (canonicalFiniteSubgroup I t ht n).ideal =
      (stageFiniteSubgroup I t ht n s i b hb hi hφ).ideal.comap
        (stageCurveRecovery I t ht n s i hi) := by
  rw [stageFiniteSubgroup_ideal]
  exact stageEmbedding_recovery_ideal I t ht n s i hi hφ

end FLT.Mazur.OneGonAdicIndependentModel
