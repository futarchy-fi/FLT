/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonCoefficientIso
public import FLT.Mazur.OneGonAdicIndependentStageRecovery
public import FLT.Mazur.OverPullbackTowerComparison
public import FLT.Mazur.GeneralizedCurveBaseChangeCompEq

/-!
# Full generalized-curve recovery of the finite smooth-stage model

The original complete arithmetic one-gon is the actual pullback of the enlarged
finite coefficient model as a generalized elliptic curve. Its whole-curve
projection agrees with the previously constructed Cartesian recovery map.
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

/-- The arbitrary stage tower recovers the actual original coefficient inclusion. -/
theorem stageBaseMap_comp :
    baseMap (stageBase I t ht n s i) R ≫ stageBaseMap I t ht n s i =
      baseMap (base I t ht n s) R := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- Recover the finite smooth-stage model with its entire arithmetic group action. -/
irreducible_def stageGeneralizedRecoveryIso :
    ArithmeticOneGonGeneralizedCurve.curve t (complementaryFactor_isUnit I t ht) ≅
      (stageCurve I t ht n s i hi).baseChange (baseMap (stageBase I t ht n s i) R) :=
  ArithmeticOneGonGeneralizedCurve.coefficientIso (S := R)
    (parameter I t ht n s) (parameter_complementaryUnit I t ht n s hi) ≪≫
      (curve I t ht n s hi).baseChangeCompEqIso (stageBaseMap I t ht n s i)
        (baseMap (stageBase I t ht n s i) R) (baseMap (base I t ht n s) R)
        (stageBaseMap_comp I t ht n s i).symm

/-- Full DR recovery retains the initial whole-cubic coefficient projection. -/
@[reassoc] theorem stageGeneralizedRecoveryIso_fst_fst :
    (stageGeneralizedRecoveryIso I t ht n s i hi).hom.curve.left ≫
      pullback.fst (stageCurve I t ht n s i hi).curve.hom
        (baseMap (stageBase I t ht n s i) R) ≫
          pullback.fst (curve I t ht n s hi).curve.hom (stageBaseMap I t ht n s i) =
            projection I t ht n s := by
  rw [stageGeneralizedRecoveryIso_def]
  change (_ ≫ _) ≫ _ ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (ArithmeticOneGonGeneralizedCurve.coefficientIso (S := R)
      (parameter I t ht n s) (parameter_complementaryUnit I t ht n s hi)).hom.curve.left
        ≫ f) (baseChangeCompEqIso_curve_fst (curve I t ht n s hi)
          (stageBaseMap I t ht n s i) (baseMap (stageBase I t ht n s i) R)
          (baseMap (base I t ht n s) R) (stageBaseMap_comp I t ht n s i).symm)).trans
      (ArithmeticOneGonGeneralizedCurve.coefficientIso_curve_fst _ _))

/-- The full comparison recovers exactly the existing enlarged whole-curve map. -/
@[reassoc] theorem stageGeneralizedRecoveryIso_fst :
    (stageGeneralizedRecoveryIso I t ht n s i hi).hom.curve.left ≫
      pullback.fst (stageCurve I t ht n s i hi).curve.hom
        (baseMap (stageBase I t ht n s i) R) = stageCurveRecovery I t ht n s i hi := by
  apply pullback.hom_ext
  · rw [Category.assoc, stageCurveRecovery_fst]
    exact stageGeneralizedRecoveryIso_fst_fst I t ht n s i hi
  · change (_ ≫ _) ≫ (stageCurve I t ht n s i hi).curve.hom =
      stageCurveRecovery I t ht n s i hi ≫ (stageCurve I t ht n s i hi).curve.hom
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have hw := (stageGeneralizedRecoveryIso I t ht n s i hi).hom.curve.w
    change _ ≫ pullback.snd _ _ = _ at hw
    rw [hw, (stageCurveRecovery_isPullback I t ht n s i hi).w]
    rfl

/-- The original character source recovers the arbitrary stage through its actual tower. -/
def stageFullSourceIso : model R (ZMod n) ≅
    (Over.pullback (baseMap (stageBase I t ht n s i) R)).obj (stageCarrier I t ht n s i) :=
  overIso (base I t ht n s) R (ZMod n) ≪≫
    (OverPullbackCoherence.towerIso (stageBaseMap I t ht n s i)
      (baseMap (stageBase I t ht n s i) R) (baseMap (base I t ht n s) R)
      (stageBaseMap_comp I t ht n s i)).app (carrier I t ht n s)

/-- The constructed source isomorphism retains the initial character coefficient projection. -/
@[reassoc] theorem stageFullSourceIso_fst_fst :
    (stageFullSourceIso I t ht n s i).hom.left ≫
      pullback.fst (stageCarrier I t ht n s i).hom (baseMap (stageBase I t ht n s i) R) ≫
        pullback.fst (carrier I t ht n s).hom (stageBaseMap I t ht n s i) =
          sourceProjection I t ht n s := by
  change (_ ≫ _) ≫ _ ≫ _ = _
  rw [Category.assoc]
  exact (congrArg (fun f => (overIso (base I t ht n s) R (ZMod n)).hom.left ≫ f)
    (OverPullbackCoherence.towerIso_fst_fst (stageBaseMap I t ht n s i)
      (baseMap (stageBase I t ht n s i) R) (baseMap (base I t ht n s) R)
      (stageBaseMap_comp I t ht n s i) (carrier I t ht n s))).trans (overIso_fst _ _ _)

/-- The full source isomorphism projects to the actual stage recovery morphism. -/
@[reassoc] theorem stageFullSourceIso_fst :
    (stageFullSourceIso I t ht n s i).hom.left ≫
      pullback.fst (stageCarrier I t ht n s i).hom (baseMap (stageBase I t ht n s i) R) =
        stageSourceRecovery I t ht n s i := by
  apply pullback.hom_ext
  · rw [Category.assoc, stageSourceRecovery_fst]
    exact stageFullSourceIso_fst_fst I t ht n s i
  · change (_ ≫ _) ≫ (stageCarrier I t ht n s i).hom =
      stageSourceRecovery I t ht n s i ≫ (stageCarrier I t ht n s i).hom
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have hw := (stageFullSourceIso I t ht n s i).hom.w
    change _ ≫ pullback.snd _ _ = _ at hw
    rw [hw, (stageSourceRecovery_isPullback I t ht n s i).w]
    rfl

/-- The entire canonical embedding is recovered for arbitrary independent support and stage. -/
theorem stage_full_embedding_recovery :
    (stageFullSourceIso I t ht n s i).hom ≫
      (Over.pullback (baseMap (stageBase I t ht n s i) R)).map
        (stageEmbedding I t ht n s i hi) =
      (canonicalFiniteSubgroup I t ht n).curveMap ≫
        (stageGeneralizedRecoveryIso I t ht n s i hi).hom.curve := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst]
    rw [← Category.assoc, stageFullSourceIso_fst, stageGeneralizedRecoveryIso_fst]
    exact stageEmbedding_recovery I t ht n s i hi
  · exact (Over.w _).trans (Over.w _).symm

end FLT.Mazur.OneGonAdicIndependentModel
