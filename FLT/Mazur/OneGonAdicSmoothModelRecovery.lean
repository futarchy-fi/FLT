/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicSmoothModelClosed
public import FLT.Mazur.CoefficientModelActualRecovery

/-!
# Cartesian recovery of the enlarged smooth model

The coefficient enlargement retains both original projections. Recovery of
its closed whole-cubic embedding gives the actual canonical embedding and
the full canonical ideal, including every infinitesimal multiplicity.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart Approximation CharacterSchemeBaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n]

/-- The original complete cubic is the actual recovery of the finite coefficient cubic. -/
def algebraicCurveRecovery :
    (ArithmeticOneGonGeneralizedCurve.curve t (complementaryFactor_isUnit I t ht)).curve.left ≅
      (coefficientModelCone (algebraicBase I t ht n) (algebraicCurve I t ht n).curve.hom).pt :=
  (coefficient_isPullback (S := R) (algebraicParameter I t ht n)).isoPullback

/-- Projection from the original complete character source to the enlarged source. -/
def smoothModelSourceRecovery : (model R (ZMod n)).left ⟶ (smoothModelCarrier I t ht n).left :=
  coefficientActualRecovery (algebraicBase I t ht n) (algebraicCarrier I t ht n).hom
    (algebraicSourceRecovery I t ht n) (algebraicSmoothStage I t ht n)

/-- Projection from the original complete cubic to the enlarged whole cubic. -/
def smoothModelCurveRecovery :
    (ArithmeticOneGonGeneralizedCurve.curve t (complementaryFactor_isUnit I t ht)).curve.left ⟶
      (smoothModelCurve I t ht n).curve.left :=
  coefficientActualRecovery (algebraicBase I t ht n) (algebraicCurve I t ht n).curve.hom
    (algebraicCurveRecovery I t ht n) (algebraicSmoothStage I t ht n)

/-- The source projection still retains the original character coefficient map. -/
@[reassoc] theorem smoothModelSourceRecovery_fst :
    smoothModelSourceRecovery I t ht n ≫
      pullback.fst (algebraicCarrier I t ht n).hom (smoothModelBaseMap I t ht n) =
        algebraicSourceProjection I t ht n := by
  exact (coefficientActualRecovery_fst (algebraicBase I t ht n)
    (algebraicCarrier I t ht n).hom (algebraicSourceRecovery I t ht n)
    (algebraicSmoothStage I t ht n)).trans
      (coefficientMap_isPullback (algebraicBase I t ht n) R (ZMod n)).isoPullback_hom_fst

/-- The curve projection still retains the original whole-cubic coefficient map. -/
@[reassoc] theorem smoothModelCurveRecovery_fst :
    smoothModelCurveRecovery I t ht n ≫
      pullback.fst (algebraicCurve I t ht n).curve.hom (smoothModelBaseMap I t ht n) =
        algebraicProjection I t ht n := by
  exact (coefficientActualRecovery_fst (algebraicBase I t ht n)
    (algebraicCurve I t ht n).curve.hom (algebraicCurveRecovery I t ht n)
    (algebraicSmoothStage I t ht n)).trans
      (coefficient_isPullback (S := R) (algebraicParameter I t ht n)).isoPullback_hom_fst

/-- The original complete source is Cartesian over the enlarged character source. -/
theorem smoothModelSourceRecovery_isPullback :
    IsPullback (smoothModelSourceRecovery I t ht n) (model R (ZMod n)).hom
      (smoothModelCarrier I t ht n).hom
      ((coefficientSpectrumCone (algebraicBase I t ht n)).π.app
        (algebraicSmoothStage I t ht n)) := by
  have h := coefficientActualRecovery_isPullback (algebraicBase I t ht n)
    (algebraicCarrier I t ht n).hom (algebraicSourceRecovery I t ht n)
    (algebraicSmoothStage I t ht n)
  have hs : (algebraicSourceRecovery I t ht n).hom ≫
      pullback.snd (algebraicCarrier I t ht n).hom
        (Spec.map (CommRingCat.ofHom (algebraicBase I t ht n).val.toRingHom)) =
          (model R (ZMod n)).hom :=
    (coefficientMap_isPullback (algebraicBase I t ht n) R (ZMod n)).isoPullback_hom_snd
  rw [hs] at h
  exact h

/-- The original complete curve is Cartesian over the enlarged whole cubic. -/
theorem smoothModelCurveRecovery_isPullback :
    IsPullback (smoothModelCurveRecovery I t ht n) (family t).hom
      (smoothModelCurve I t ht n).curve.hom
      ((coefficientSpectrumCone (algebraicBase I t ht n)).π.app
        (algebraicSmoothStage I t ht n)) := by
  have h := coefficientActualRecovery_isPullback (algebraicBase I t ht n)
    (algebraicCurve I t ht n).curve.hom (algebraicCurveRecovery I t ht n)
    (algebraicSmoothStage I t ht n)
  have hs : (algebraicCurveRecovery I t ht n).hom ≫
      pullback.snd (algebraicCurve I t ht n).curve.hom
        (Spec.map (CommRingCat.ofHom (algebraicBase I t ht n).val.toRingHom)) =
          (family t).hom :=
    (coefficient_isPullback (S := R) (algebraicParameter I t ht n)).isoPullback_hom_snd
  rw [hs] at h
  exact h

/-- The enlarged embedding recovers the exact original canonical whole-cubic map. -/
theorem smoothModelEmbedding_recovery :
    smoothModelSourceRecovery I t ht n ≫ (smoothModelEmbedding I t ht n).left =
      (canonicalFiniteSubgroup I t ht n).curveMap.left ≫ smoothModelCurveRecovery I t ht n := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    change _ ≫ pullback.lift _ _ _ ≫ _ = _
    rw [pullback.lift_fst, ← Category.assoc, smoothModelSourceRecovery_fst,
      Category.assoc, smoothModelCurveRecovery_fst]
    exact (algebraicEmbedding_isPullback I t ht n).w
  · change (smoothModelSourceRecovery I t ht n ≫ (smoothModelEmbedding I t ht n).left) ≫
      (smoothModelCurve I t ht n).curve.hom =
        ((canonicalFiniteSubgroup I t ht n).curveMap.left ≫
          smoothModelCurveRecovery I t ht n) ≫ (smoothModelCurve I t ht n).curve.hom
    rw [Category.assoc, (smoothModelEmbedding I t ht n).w,
      (smoothModelSourceRecovery_isPullback I t ht n).w,
      Category.assoc, (smoothModelCurveRecovery_isPullback I t ht n).w,
      ← Category.assoc]
    exact congrArg (fun f => f ≫ (coefficientSpectrumCone (algebraicBase I t ht n)).π.app
      (algebraicSmoothStage I t ht n)) (canonicalFiniteSubgroup I t ht n).curveMap.w.symm

/-- The entire canonical closed embedding is recovered by a Cartesian square. -/
theorem smoothModelEmbedding_recovery_isPullback :
    IsPullback (smoothModelSourceRecovery I t ht n)
      (canonicalFiniteSubgroup I t ht n).curveMap.left (smoothModelEmbedding I t ht n).left
      (smoothModelCurveRecovery I t ht n) := by
  have h := smoothModelSourceRecovery_isPullback I t ht n
  have hw : (canonicalFiniteSubgroup I t ht n).curveMap.left ≫ (family t).hom =
      (model R (ZMod n)).hom := (canonicalFiniteSubgroup I t ht n).curveMap.w
  rw [← hw,
    ← (smoothModelEmbedding I t ht n).w] at h
  exact h.of_bot (smoothModelEmbedding_recovery I t ht n)
    (smoothModelCurveRecovery_isPullback I t ht n)

/-- Recovery preserves the full canonical ideal, with no reduction or radical. -/
theorem smoothModelEmbedding_recovery_ideal :
    (canonicalFiniteSubgroup I t ht n).ideal =
      (smoothModelEmbedding I t ht n).left.ker.comap (smoothModelCurveRecovery I t ht n) := by
  rw [smoothModelEmbedding_ideal, ← Scheme.IdealSheafData.comap_comp,
    smoothModelCurveRecovery_fst]
  exact algebraicEmbedding_ideal I t ht n

end FLT.Mazur.OneGonAdicCharacterTower
