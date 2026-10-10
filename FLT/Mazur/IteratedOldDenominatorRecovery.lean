/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IteratedQuotientOldDenominator

/-!
# Original recovery for literal old-denominator projections

Project the same unquotiented double localization to the original double open.
Its kernel is exactly the twice extended full ambient ideal, and every finite
old-denominator projection recovers this map on the entire source ring.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.IteratedQuotientProjection

universe u v

variable (R : Type u) [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P) (r : P) (b : Finset I) (d : FiniteRelationLocalization.Stage I r b)

/-- The representative projects to the literal original coordinate denominator. -/
theorem projection_oldDenominatorRepresentative_original :
    PrincipalQuotientProjection.projection I r (oldDenominatorRepresentative I r b d) =
      FiniteRelationLocalization.toQuotient R I r b d := by
  rw [← FiniteRelationLocalization.toQuotient_projection R I r b,
    projection_oldDenominatorRepresentative]

/-- The original double open inverts the chosen representative's projected denominator. -/
instance oldDenominatorOriginal_away :
    IsLocalization.Away
      (PrincipalQuotientProjection.projection I r (oldDenominatorRepresentative I r b d))
      (FiniteRelationIterated.Quotient R I r b d) := by
  rw [projection_oldDenominatorRepresentative_original R I r b d]
  infer_instance

/-- Projection from the unquotiented double localization to the literal original double open. -/
def oldDenominatorOriginalProjection :
    Localization.Away (oldDenominatorRepresentative I r b d) →ₐ[R]
      FiniteRelationIterated.Quotient R I r b d := by
  let _ : IsLocalization.Away
      (PrincipalQuotientProjection.projectionAlgHom R I r
        (oldDenominatorRepresentative I r b d))
      (FiniteRelationIterated.Quotient R I r b d) := oldDenominatorOriginal_away R I r b d
  exact IsLocalization.Away.mapₐ _ _ (PrincipalQuotientProjection.projectionAlgHom R I r)
    (oldDenominatorRepresentative I r b d)

/-- Original projection preserves all first-level numerator formulas. -/
@[simp] theorem oldDenominatorOriginalProjection_algebraMap (x : Localization.Away r) :
    oldDenominatorOriginalProjection R I r b d (algebraMap _ _ x) =
      algebraMap _ (FiniteRelationIterated.Quotient R I r b d)
        (PrincipalQuotientProjection.projection I r x) := by
  simp [oldDenominatorOriginalProjection, IsLocalization.Away.mapₐ, IsLocalization.Away.map,
    PrincipalQuotientProjection.projectionAlgHom]

/-- Every finite literal projection recovers the original projection on the full ring. -/
theorem oldDenominatorProjection_toQuotient (t : Set.Ici b) :
    (FiniteRelationIterated.toQuotient R I r b d t).comp
      (oldDenominatorProjection R I r b d t) =
      oldDenominatorOriginalProjection R I r b d := by
  apply IsLocalization.algHom_ext (Submonoid.powers (oldDenominatorRepresentative I r b d))
  apply DFunLike.ext
  intro x
  change FiniteRelationIterated.toQuotient R I r b d t
    (oldDenominatorProjection R I r b d t (algebraMap _ _ x)) =
      oldDenominatorOriginalProjection R I r b d (algebraMap _ _ x)
  rw [oldDenominatorProjection_algebraMap, FiniteRelationIterated.toQuotient_algebraMap,
    FiniteRelationLocalization.toQuotient_projection,
    oldDenominatorOriginalProjection_algebraMap]

/-- The literal original projection kills exactly the twice extended full ambient ideal. -/
theorem ker_oldDenominatorOriginalProjection :
    RingHom.ker (oldDenominatorOriginalProjection R I r b d).toRingHom =
      (I.map (algebraMap P (Localization.Away r))).map
        (algebraMap (Localization.Away r)
          (Localization.Away (oldDenominatorRepresentative I r b d))) := by
  have h : (Submonoid.powers (oldDenominatorRepresentative I r b d)).map
      (PrincipalQuotientProjection.projection I r) =
      Submonoid.powers (FiniteRelationLocalization.toQuotient R I r b d) := by
    rw [Submonoid.map_powers, projection_oldDenominatorRepresentative_original R I r b d]
  have hk := IsLocalization.ker_map
    (S := Localization.Away (oldDenominatorRepresentative I r b d))
    (FiniteRelationIterated.Quotient R I r b d)
    (PrincipalQuotientProjection.projection I r) h
  change RingHom.ker (oldDenominatorOriginalProjection R I r b d).toRingHom =
    (RingHom.ker (PrincipalQuotientProjection.projection I r)).map _ at hk
  simpa only [PrincipalQuotientProjection.ker_projection] using hk

end FLT.Mazur.IteratedQuotientProjection
