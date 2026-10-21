/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicIndependentCommonCurve
public import FLT.Mazur.OneGonAdicIndependentCurveTower
public import FLT.Mazur.ArithmeticOneGonCommonCoefficientTower

/-!
# Full recovery of the common independent coefficient comparison

The common full-curve comparison commutes with the two original recoveries.
Consequently the entire canonical subgroup embeddings agree after recovery;
this is derived from the constructed maps rather than supplied as a hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicIndependentModel
open Approximation OneGonAdicCharacterTower OneGonSmoothing CharacterSchemeBaseChange
open ArithmeticOneGonGeneralizedCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s u : Set R)
  (i : (CoefficientStage (base I t ht n s))ᵒᵖ)
  (j : (CoefficientStage (base I t ht n u))ᵒᵖ)
  (hs : complementaryInverse I t ht ∈ s) (hu : complementaryInverse I t ht ∈ u)

/-- The literal common-stage full comparison commutes with original arithmetic recovery. -/
theorem commonCurveIso_recovery :
    (stageGeneralizedRecoveryIso I t ht n s (commonLeft I t ht n s u i j) hs).hom ≫
      (GeneralizedEllipticCurve.baseChangeFunctor (baseMap (commonBase I t ht n s u i j) R)).map
        (commonCurveIso I t ht n s u i j hs hu).hom =
      (stageGeneralizedRecoveryIso I t ht n u (commonRight I t ht n s u i j) hu).hom := by
  let _ := commonLeftAlgebra I t ht n s u i j
  let _ := commonRightAlgebra I t ht n s u i j
  rw [stageGeneralizedRecoveryIso_tower, stageGeneralizedRecoveryIso_tower, commonCurveIso_def]
  have h := @commonCoefficientIso_tower_recovery
    (base I t ht n s) (base I t ht n u) (commonBase I t ht n s u i j) R _ _ _ _
    (commonLeftAlgebra I t ht n s u i j) (commonRightAlgebra I t ht n s u i j) _ _ _
    (IsScalarTower.of_algebraMap_eq (fun _ => rfl))
    (IsScalarTower.of_algebraMap_eq (fun _ => rfl))
    (parameter I t ht n s) (parameter I t ht n u)
    (parameter_complementaryUnit I t ht n s hs)
    (parameter_complementaryUnit I t ht n u hu) (common_parameter_eq I t ht n s u i j)
  simpa only [parameterIso_def, Iso.refl_hom, Category.id_comp,
    stageBase, commonLeft, commonRight, stageBaseAlgebra, commonLeftAlgebra,
    commonRightAlgebra] using h

/-- The common comparison identifies the two full recovered canonical embeddings. -/
theorem common_embedding_recovery :
    (overIso (commonBase I t ht n s u i j) R (ZMod n)).hom ≫
      (Over.pullback (baseMap (commonBase I t ht n s u i j) R)).map
        (((stageCharacterIso I t ht n s (commonLeft I t ht n s u i j)).hom ≫
          stageEmbedding I t ht n s (commonLeft I t ht n s u i j) hs) ≫
            (commonCurveIso I t ht n s u i j hs hu).hom.curve) =
    (overIso (commonBase I t ht n s u i j) R (ZMod n)).hom ≫
      (Over.pullback (baseMap (commonBase I t ht n s u i j) R)).map
        ((stageCharacterIso I t ht n u (commonRight I t ht n s u i j)).hom ≫
          stageEmbedding I t ht n u (commonRight I t ht n s u i j) hu) := by
  rw [Functor.map_comp, ← Category.assoc]
  erw [stage_intrinsic_embedding_recovery I t ht n s (commonLeft I t ht n s u i j) hs,
    stage_intrinsic_embedding_recovery I t ht n u (commonRight I t ht n s u i j) hu]
  have hc := congrArg (fun f => f.curve) (commonCurveIso_recovery I t ht n s u i j hs hu)
  change (stageGeneralizedRecoveryIso I t ht n s (commonLeft I t ht n s u i j) hs).hom.curve ≫
      (Over.pullback (baseMap (commonBase I t ht n s u i j) R)).map
        (commonCurveIso I t ht n s u i j hs hu).hom.curve =
      (stageGeneralizedRecoveryIso I t ht n u (commonRight I t ht n s u i j) hu).hom.curve at hc
  rw [Category.assoc, hc]

end FLT.Mazur.OneGonAdicIndependentModel
