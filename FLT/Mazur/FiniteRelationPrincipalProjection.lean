/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationLocalizationStages
public import FLT.Mazur.PrincipalQuotientProjection

/-!
# Canonical projection compatibility for finite principal stages

Projecting an unquotiented principal element through any finite relation stage
agrees with its projection to the full original quotient.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationLocalization

universe u v

variable (R : Type u) [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P) (r : P) (s : Finset I)

/-- Original recovery commutes with the canonical principal quotient projection. -/
theorem toQuotient_comp_projection :
    (toQuotient R I r s).toRingHom.comp
        (PrincipalQuotientProjection.projection (FiniteRelationModel.relations I s) r) =
      PrincipalQuotientProjection.projection I r := by
  apply IsLocalization.ringHom_ext (Submonoid.powers r)
  ext p
  change toQuotient R I r s
    (PrincipalQuotientProjection.projection (FiniteRelationModel.relations I s) r
      (algebraMap P (Localization.Away r) p)) =
    PrincipalQuotientProjection.projection I r (algebraMap P (Localization.Away r) p)
  rw [PrincipalQuotientProjection.projection_algebraMap,
    PrincipalQuotientProjection.projection_algebraMap, toQuotient_algebraMap]
  rfl

/-- Compatibility applies to entire localized rings, including inverse coordinates. -/
@[simp] theorem toQuotient_projection (x : Localization.Away r) :
    toQuotient R I r s
      (PrincipalQuotientProjection.projection (FiniteRelationModel.relations I s) r x) =
      PrincipalQuotientProjection.projection I r x :=
  RingHom.congr_fun (toQuotient_comp_projection R I r s) x

end FLT.Mazur.FiniteRelationLocalization
