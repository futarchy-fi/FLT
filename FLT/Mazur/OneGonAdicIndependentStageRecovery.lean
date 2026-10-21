/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicIndependentStageModel
public import FLT.Mazur.CoefficientModelActualRecovery

/-!
# Cartesian recovery of the enlarged smooth model

The coefficient enlargement retains both original projections. Recovery of
its closed whole-cubic embedding gives the actual canonical embedding and
the full canonical ideal, including every infinitesimal multiplicity.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicIndependentModel

open OneGonAdicCharacterTower
open OneGonSmoothing WeierstrassIntegralChart Approximation CharacterSchemeBaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s : Set R)
  (i : (CoefficientStage (base I t ht n s))ᵒᵖ)
  (hi : complementaryInverse I t ht ∈ s)

/-- The original complete cubic is the actual recovery of the finite coefficient cubic. -/
def curveRecovery :
    (ArithmeticOneGonGeneralizedCurve.curve t (complementaryFactor_isUnit I t ht)).curve.left ≅
      (coefficientModelCone (base I t ht n s) (curve I t ht n s hi).curve.hom).pt :=
  (coefficient_isPullback (S := R) (parameter I t ht n s)).isoPullback

/-- Projection from the original complete character source to the enlarged source. -/
def stageSourceRecovery : (model R (ZMod n)).left ⟶ (stageCarrier I t ht n s i).left :=
  coefficientActualRecovery (base I t ht n s) (carrier I t ht n s).hom
    (sourceRecovery I t ht n s) i

/-- Projection from the original complete cubic to the enlarged whole cubic. -/
def stageCurveRecovery :
    (ArithmeticOneGonGeneralizedCurve.curve t (complementaryFactor_isUnit I t ht)).curve.left ⟶
      (stageCurve I t ht n s i hi).curve.left :=
  coefficientActualRecovery (base I t ht n s) (curve I t ht n s hi).curve.hom
    (curveRecovery I t ht n s hi) i

/-- The source projection still retains the original character coefficient map. -/
@[reassoc] theorem stageSourceRecovery_fst :
    stageSourceRecovery I t ht n s i ≫
      pullback.fst (carrier I t ht n s).hom (stageBaseMap I t ht n s i) =
        sourceProjection I t ht n s := by
  exact (coefficientActualRecovery_fst (base I t ht n s)
    (carrier I t ht n s).hom (sourceRecovery I t ht n s)
    i).trans
      (coefficientMap_isPullback (base I t ht n s) R (ZMod n)).isoPullback_hom_fst

/-- The curve projection still retains the original whole-cubic coefficient map. -/
@[reassoc] theorem stageCurveRecovery_fst :
    stageCurveRecovery I t ht n s i hi ≫
      pullback.fst (curve I t ht n s hi).curve.hom (stageBaseMap I t ht n s i) =
        projection I t ht n s := by
  exact (coefficientActualRecovery_fst (base I t ht n s)
    (curve I t ht n s hi).curve.hom (curveRecovery I t ht n s hi)
    i).trans
      (coefficient_isPullback (S := R) (parameter I t ht n s)).isoPullback_hom_fst

/-- The original complete source is Cartesian over the enlarged character source. -/
theorem stageSourceRecovery_isPullback :
    IsPullback (stageSourceRecovery I t ht n s i) (model R (ZMod n)).hom
      (stageCarrier I t ht n s i).hom
      ((coefficientSpectrumCone (base I t ht n s)).π.app
        i) := by
  have h := coefficientActualRecovery_isPullback (base I t ht n s)
    (carrier I t ht n s).hom (sourceRecovery I t ht n s)
    i
  have hs : (sourceRecovery I t ht n s).hom ≫
      pullback.snd (carrier I t ht n s).hom
        (Spec.map (CommRingCat.ofHom (base I t ht n s).val.toRingHom)) =
          (model R (ZMod n)).hom :=
    (coefficientMap_isPullback (base I t ht n s) R (ZMod n)).isoPullback_hom_snd
  rw [hs] at h
  exact h

/-- The original complete curve is Cartesian over the enlarged whole cubic. -/
theorem stageCurveRecovery_isPullback :
    IsPullback (stageCurveRecovery I t ht n s i hi) (family t).hom
      (stageCurve I t ht n s i hi).curve.hom
      ((coefficientSpectrumCone (base I t ht n s)).π.app
        i) := by
  have h := coefficientActualRecovery_isPullback (base I t ht n s)
    (curve I t ht n s hi).curve.hom (curveRecovery I t ht n s hi)
    i
  have hs : (curveRecovery I t ht n s hi).hom ≫
      pullback.snd (curve I t ht n s hi).curve.hom
        (Spec.map (CommRingCat.ofHom (base I t ht n s).val.toRingHom)) =
          (family t).hom :=
    (coefficient_isPullback (S := R) (parameter I t ht n s)).isoPullback_hom_snd
  rw [hs] at h
  exact h

/-- The enlarged embedding recovers the exact original canonical whole-cubic map. -/
theorem stageEmbedding_recovery :
    stageSourceRecovery I t ht n s i ≫ (stageEmbedding I t ht n s i hi).left =
      (canonicalFiniteSubgroup I t ht n).curveMap.left ≫ stageCurveRecovery I t ht n s i hi := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    change _ ≫ pullback.lift _ _ _ ≫ _ = _
    rw [pullback.lift_fst, ← Category.assoc, stageSourceRecovery_fst,
      Category.assoc, stageCurveRecovery_fst]
    exact (embedding_isPullback I t ht n s).w
  · change (stageSourceRecovery I t ht n s i ≫ (stageEmbedding I t ht n s i hi).left) ≫
      (stageCurve I t ht n s i hi).curve.hom =
        ((canonicalFiniteSubgroup I t ht n).curveMap.left ≫
          stageCurveRecovery I t ht n s i hi) ≫ (stageCurve I t ht n s i hi).curve.hom
    rw [Category.assoc, (stageEmbedding I t ht n s i hi).w,
      (stageSourceRecovery_isPullback I t ht n s i).w,
      Category.assoc, (stageCurveRecovery_isPullback I t ht n s i hi).w,
      ← Category.assoc]
    exact congrArg (fun f => f ≫ (coefficientSpectrumCone (base I t ht n s)).π.app
      i) (canonicalFiniteSubgroup I t ht n).curveMap.w.symm

/-- The entire canonical closed embedding is recovered by a Cartesian square. -/
theorem stageEmbedding_recovery_isPullback :
    IsPullback (stageSourceRecovery I t ht n s i)
      (canonicalFiniteSubgroup I t ht n).curveMap.left (stageEmbedding I t ht n s i hi).left
      (stageCurveRecovery I t ht n s i hi) := by
  have h := stageSourceRecovery_isPullback I t ht n s i
  have hw : (canonicalFiniteSubgroup I t ht n).curveMap.left ≫ (family t).hom =
      (model R (ZMod n)).hom := (canonicalFiniteSubgroup I t ht n).curveMap.w
  rw [← hw,
    ← (stageEmbedding I t ht n s i hi).w] at h
  exact h.of_bot (stageEmbedding_recovery I t ht n s i hi)
    (stageCurveRecovery_isPullback I t ht n s i hi)

/-- The arbitrary stage embedding is the base change of its independent support embedding. -/
theorem stageEmbedding_isPullback :
    IsPullback (stageEmbedding I t ht n s i hi).left
      (pullback.fst (carrier I t ht n s).hom (stageBaseMap I t ht n s i))
      (pullback.fst (curve I t ht n s hi).curve.hom (stageBaseMap I t ht n s i))
      (embedding I t ht n s) :=
  OverPullbackLocalPushout.map_isPullback (stageBaseMap I t ht n s i)
    (Over.homMk (U := carrier I t ht n s) (V := (curve I t ht n s hi).curve)
      (embedding I t ht n s) (embedding_structure I t ht n s))

/-- Surjective support coordinates give a closed whole embedding at every stage. -/
theorem stageEmbedding_isClosedImmersion
    (hφ : Function.Surjective (OneGonFiniteCoefficientCoordinates.modelCoordinates t 1
      (canonicalCoordinates I t ht n) s)) :
    IsClosedImmersion (stageEmbedding I t ht n s i hi).left :=
  MorphismProperty.of_isPullback (stageEmbedding_isPullback I t ht n s i hi).flip
    (embedding_isClosedImmersion I t ht n s hφ)

/-- Recovery identifies the full ideal at every independent support and stage. -/
theorem stageEmbedding_recovery_ideal
    (hφ : Function.Surjective (OneGonFiniteCoefficientCoordinates.modelCoordinates t 1
      (canonicalCoordinates I t ht n) s)) :
    (canonicalFiniteSubgroup I t ht n).ideal =
      (stageEmbedding I t ht n s i hi).left.ker.comap (stageCurveRecovery I t ht n s i hi) := by
  let _ := stageEmbedding_isClosedImmersion I t ht n s i hi hφ
  change (canonicalFiniteSubgroup I t ht n).curveMap.left.ker = _
  have h := (stageEmbedding_recovery_isPullback I t ht n s i hi).flip
  rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
  exact Scheme.IdealSheafData.ker_fst_of_isClosedImmersion _ _

end FLT.Mazur.OneGonAdicIndependentModel
