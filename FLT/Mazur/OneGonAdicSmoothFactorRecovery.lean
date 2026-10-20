/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicSmoothModelRecovery

/-!
# Recovery retains the actual canonical smooth factor

The enlarged smooth group recovers by the same coefficient square as the
whole cubic. Its descended closed factor is precisely the original canonical
smooth map after this projection, before any descent of homomorphism laws.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart Approximation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n]

/-- The complete smooth group is the recovery of the original coefficient smooth group. -/
def algebraicSmoothRecovery : (integralSmoothOpen (equation t)).toScheme ≅
    (coefficientModelCone (algebraicBase I t ht n) (algebraicCurve I t ht n).group.hom).pt :=
  (smoothCoefficientProjection_isPullback (S := R) (algebraicParameter I t ht n)).isoPullback

/-- The actual smooth-group projection to the enlarged finite coefficient model. -/
def smoothModelGroupRecovery : (integralSmoothOpen (equation t)).toScheme ⟶
    (smoothModelCurve I t ht n).group.left :=
  coefficientActualRecovery (algebraicBase I t ht n) (algebraicCurve I t ht n).group.hom
    (algebraicSmoothRecovery I t ht n) (algebraicSmoothStage I t ht n)

/-- Projection retains the original smooth coefficient comparison. -/
@[reassoc] theorem smoothModelGroupRecovery_fst :
    smoothModelGroupRecovery I t ht n ≫
      pullback.fst (algebraicCurve I t ht n).group.hom (smoothModelBaseMap I t ht n) =
        smoothCoefficientProjection (S := R) (algebraicParameter I t ht n) := by
  exact (coefficientActualRecovery_fst (algebraicBase I t ht n)
    (algebraicCurve I t ht n).group.hom (algebraicSmoothRecovery I t ht n)
    (algebraicSmoothStage I t ht n)).trans
      (smoothCoefficientProjection_isPullback (S := R)
        (algebraicParameter I t ht n)).isoPullback_hom_fst

/-- The actual smooth-group projection is Cartesian over the original complete base. -/
theorem smoothModelGroupRecovery_isPullback :
    IsPullback (smoothModelGroupRecovery I t ht n) (integralSmoothStructure (equation t))
      (smoothModelCurve I t ht n).group.hom
      ((coefficientSpectrumCone (algebraicBase I t ht n)).π.app
        (algebraicSmoothStage I t ht n)) := by
  have h := coefficientActualRecovery_isPullback (algebraicBase I t ht n)
    (algebraicCurve I t ht n).group.hom (algebraicSmoothRecovery I t ht n)
    (algebraicSmoothStage I t ht n)
  have hs : (algebraicSmoothRecovery I t ht n).hom ≫
      pullback.snd (algebraicCurve I t ht n).group.hom
        (Spec.map (CommRingCat.ofHom (algebraicBase I t ht n).val.toRingHom)) =
          integralSmoothStructure (equation t) :=
    (smoothCoefficientProjection_isPullback (S := R)
      (algebraicParameter I t ht n)).isoPullback_hom_snd
  rw [hs] at h
  exact h

/-- Recovery of the descended smooth factor is exactly the original canonical smooth map. -/
theorem smoothModelFactor_recovery :
    smoothModelSourceRecovery I t ht n ≫ (smoothModelFactor I t ht n).left =
      effectiveSmooth I t ht (initialRootsHom n I t ht) ≫ smoothModelGroupRecovery I t ht n := by
  apply pullback.hom_ext
  · rw [Category.assoc, smoothModelFactor_fst]
    change ((algebraicSourceRecovery I t ht n).hom ≫ _) ≫ _ = _
    rw [Category.assoc, algebraicSmoothFactor_recovery, recoveredSmoothFactor,
      Iso.hom_inv_id_assoc, Category.assoc, smoothModelGroupRecovery_fst]
  · change (smoothModelSourceRecovery I t ht n ≫ (smoothModelFactor I t ht n).left) ≫
      (smoothModelCurve I t ht n).group.hom =
        (effectiveSmooth I t ht (initialRootsHom n I t ht) ≫
          smoothModelGroupRecovery I t ht n) ≫ (smoothModelCurve I t ht n).group.hom
    rw [Category.assoc, (smoothModelFactor I t ht n).w,
      (smoothModelSourceRecovery_isPullback I t ht n).w,
      Category.assoc, (smoothModelGroupRecovery_isPullback I t ht n).w,
      ← Category.assoc, effectiveSmooth_structure]

/-- The original canonical smooth embedding is the Cartesian pullback of its descended factor. -/
theorem smoothModelFactor_recovery_isPullback :
    IsPullback (smoothModelSourceRecovery I t ht n)
      (effectiveSmooth I t ht (initialRootsHom n I t ht)) (smoothModelFactor I t ht n).left
      (smoothModelGroupRecovery I t ht n) := by
  have h := smoothModelSourceRecovery_isPullback I t ht n
  rw [← effectiveSmooth_structure I t ht (initialRootsHom n I t ht),
    ← (smoothModelFactor I t ht n).w] at h
  exact h.of_bot (smoothModelFactor_recovery I t ht n)
    (smoothModelGroupRecovery_isPullback I t ht n)

end FLT.Mazur.OneGonAdicCharacterTower
