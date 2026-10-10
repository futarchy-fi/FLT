/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IteratedQuotientProjection
public import FLT.Mazur.FiniteRelationPrincipalProjection

/-!
# Original recovery for canonical iterated relation stages

The projected second denominator commutes with original recovery on the first
principal open. Localizing this square recovers the entire original double open.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.IteratedQuotientProjection

universe u v

variable (R : Type u) [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P) (r : P) (s : Localization.Away r) (t : Finset I)

/-- Original recovery sends the finite second denominator to the original one. -/
instance stageToQuotient_away :
    IsLocalization.Away (FiniteRelationLocalization.toQuotient R I r t
      (PrincipalQuotientProjection.projection (FiniteRelationModel.relations I t) r s))
      (Target I r s) := by
  rw [FiniteRelationLocalization.toQuotient_projection]
  infer_instance

/-- Recovery from the literal iterated quotient at a finite relation stage. -/
def stageToQuotient : Target (FiniteRelationModel.relations I t) r s →ₐ[R] Target I r s :=
  IsLocalization.Away.mapₐ _ _ (FiniteRelationLocalization.toQuotient R I r t)
    (PrincipalQuotientProjection.projection (FiniteRelationModel.relations I t) r s)

/-- The iterated recovery map agrees with first-level recovery on every first-level numerator. -/
@[simp] theorem stageToQuotient_algebraMap
    (x : PrincipalQuotientProjection.Target (FiniteRelationModel.relations I t) r) :
    stageToQuotient R I r s t (algebraMap _ _ x) =
      algebraMap _ (Target I r s) (FiniteRelationLocalization.toQuotient R I r t x) := by
  simp [stageToQuotient, IsLocalization.Away.mapₐ, IsLocalization.Away.map]

/-- Recovery commutes with projection of the whole unquotiented double localization. -/
theorem stageToQuotient_comp_projection :
    (stageToQuotient R I r s t).toRingHom.comp
      (projection (FiniteRelationModel.relations I t) r s) = projection I r s := by
  apply IsLocalization.ringHom_ext (Submonoid.powers s)
  ext x
  change stageToQuotient R I r s t
    (projection (FiniteRelationModel.relations I t) r s
      (algebraMap _ (Localization.Away s) x)) =
    projection I r s (algebraMap _ (Localization.Away s) x)
  rw [projection_algebraMap, projection_algebraMap, stageToQuotient_algebraMap,
    FiniteRelationLocalization.toQuotient_projection]

/-- Every unquotiented fraction recovers its original value through every finite stage. -/
@[simp] theorem stageToQuotient_projection (x : Localization.Away s) :
    stageToQuotient R I r s t (projection (FiniteRelationModel.relations I t) r s x) =
      projection I r s x :=
  RingHom.congr_fun (stageToQuotient_comp_projection R I r s t) x

/-- Original double-open sections all lift to any finite iterated stage. -/
theorem stageToQuotient_surjective : Function.Surjective (stageToQuotient R I r s t) :=
  IsLocalization.Away.mapₐ_surjective_of_surjective _
    (FiniteRelationLocalization.toQuotient_surjective R I r t)

end FLT.Mazur.IteratedQuotientProjection
