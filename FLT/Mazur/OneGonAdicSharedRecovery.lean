/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicSharedCurve
public import FLT.Mazur.OneGonAdicIndependentCurveTower
public import FLT.Mazur.ArithmeticOneGonCommonCoefficientTower

/-!
# Recovery of shared-stage arithmetic comparisons

The comparison over any shared finite ring commutes with full arithmetic
recovery. The whole intrinsic subgroup embedding therefore recovers identically.
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
  (K : Subalgebra ℤ R) [Algebra.FiniteType ℤ K]
  (hS : base I t ht n s ≤ K) (hU : base I t ht n u ≤ K)
  (hs : complementaryInverse I t ht ∈ s) (hu : complementaryInverse I t ht ∈ u)

/-- The literal common-stage full comparison commutes with original arithmetic recovery. -/
theorem sharedCurveIso_recovery :
    (stageGeneralizedRecoveryIso I t ht n s (sharedStage I t ht n s K hS) hs).hom ≫
      (GeneralizedEllipticCurve.baseChangeFunctor (baseMap K R)).map
        (sharedCurveIso I t ht n s u K hS hU hs hu).hom =
      (stageGeneralizedRecoveryIso I t ht n u (sharedStage I t ht n u K hU) hu).hom := by
  let _ := sharedAlgebra I t ht n s K hS
  let _ := sharedAlgebra I t ht n u K hU
  rw [stageGeneralizedRecoveryIso_tower, stageGeneralizedRecoveryIso_tower, sharedCurveIso_def]
  have h := @commonCoefficientIso_tower_recovery
    (base I t ht n s) (base I t ht n u) K R _ _ _ _
    (sharedAlgebra I t ht n s K hS) (sharedAlgebra I t ht n u K hU) _ _ _
    (IsScalarTower.of_algebraMap_eq (fun _ => rfl))
    (IsScalarTower.of_algebraMap_eq (fun _ => rfl))
    (parameter I t ht n s) (parameter I t ht n u)
    (parameter_complementaryUnit I t ht n s hs)
    (parameter_complementaryUnit I t ht n u hu) (shared_parameter_eq I t ht n s K hS u hU)
  simpa only [parameterIso_def, Iso.refl_hom, Category.id_comp,
    stageBase, sharedStage, stageBaseAlgebra, sharedAlgebra] using h

/-- The common comparison identifies the two full recovered canonical embeddings. -/
theorem shared_embedding_recovery :
    (overIso K R (ZMod n)).hom ≫
      (Over.pullback (baseMap K R)).map
        (((stageCharacterIso I t ht n s (sharedStage I t ht n s K hS)).hom ≫
          stageEmbedding I t ht n s (sharedStage I t ht n s K hS) hs) ≫
            (sharedCurveIso I t ht n s u K hS hU hs hu).hom.curve) =
    (overIso K R (ZMod n)).hom ≫
      (Over.pullback (baseMap K R)).map
        ((stageCharacterIso I t ht n u (sharedStage I t ht n u K hU)).hom ≫
          stageEmbedding I t ht n u (sharedStage I t ht n u K hU) hu) := by
  rw [Functor.map_comp, ← Category.assoc]
  erw [stage_intrinsic_embedding_recovery I t ht n s (sharedStage I t ht n s K hS) hs,
    stage_intrinsic_embedding_recovery I t ht n u (sharedStage I t ht n u K hU) hu]
  have hc := congrArg (fun f => f.curve) (sharedCurveIso_recovery I t ht n s u K hS hU hs hu)
  change (stageGeneralizedRecoveryIso I t ht n s (sharedStage I t ht n s K hS) hs).hom.curve ≫
      (Over.pullback (baseMap K R)).map
        (sharedCurveIso I t ht n s u K hS hU hs hu).hom.curve =
      (stageGeneralizedRecoveryIso I t ht n u (sharedStage I t ht n u K hU) hu).hom.curve at hc
  rw [Category.assoc, hc]

end FLT.Mazur.OneGonAdicIndependentModel
