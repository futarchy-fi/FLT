/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationStages
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-!
# Principal localizations of finite-relation stages

Choose a denominator in the presenting ring. Localizing its image at every
stage constructs compatible finitely presented models of the principal open.
All transition and quotient maps remain surjective.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationLocalization

universe u v

variable {R : Type u} [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P) (r : P)

/-- The principal open's ring at a finite relation stage. -/
abbrev Stage (s : Finset I) :=
  Localization.Away (Ideal.Quotient.mk (FiniteRelationModel.relations I s) r)

/-- The principal open's ring in the full quotient. -/
abbrev Quotient := Localization.Away (Ideal.Quotient.mk I r)

/-- Principal localization preserves finite presentation of every model. -/
instance stage_finitePresentation [Algebra.FinitePresentation R P] (s : Finset I) :
    Algebra.FinitePresentation R (Stage I r s) := inferInstance

variable (R)

/-- The target localization inverts the transitioned denominator. -/
instance transition_away {s t : Finset I} (h : s ≤ t) :
    IsLocalization.Away
      (FiniteRelationModel.transition R I h (Ideal.Quotient.mk _ r)) (Stage I r t) := by
  rw [FiniteRelationModel.transition_mk]
  infer_instance

/-- The quotient localization inverts the projected denominator. -/
instance toQuotient_away (s : Finset I) :
    IsLocalization.Away
      (FiniteRelationModel.toQuotient R I s (Ideal.Quotient.mk _ r)) (Quotient I r) := by
  rw [FiniteRelationModel.toQuotient_mk]
  infer_instance

/-- Localized transition induced by imposing more relations. -/
def transition {s t : Finset I} (h : s ≤ t) : Stage I r s →ₐ[R] Stage I r t :=
  IsLocalization.Away.mapₐ _ _ (FiniteRelationModel.transition R I h)
    (Ideal.Quotient.mk _ r)

/-- Localized projection to the full quotient. -/
def toQuotient (s : Finset I) : Stage I r s →ₐ[R] Quotient I r :=
  IsLocalization.Away.mapₐ _ _ (FiniteRelationModel.toQuotient R I s)
    (Ideal.Quotient.mk _ r)

/-- Transition maps send each numerator to its next-stage image. -/
@[simp] theorem transition_algebraMap {s t : Finset I} (h : s ≤ t)
    (x : FiniteRelationModel.Stage I s) :
    transition R I r h (algebraMap _ (Stage I r s) x) =
      algebraMap _ (Stage I r t) (FiniteRelationModel.transition R I h x) := by
  simp [transition, IsLocalization.Away.mapₐ, IsLocalization.Away.map]

/-- The quotient projection sends each numerator to its quotient image. -/
@[simp] theorem toQuotient_algebraMap (s : Finset I) (x : FiniteRelationModel.Stage I s) :
    toQuotient R I r s (algebraMap _ (Stage I r s) x) =
      algebraMap _ (Quotient I r) (FiniteRelationModel.toQuotient R I s x) := by
  simp [toQuotient, IsLocalization.Away.mapₐ, IsLocalization.Away.map]

/-- Localized transitions are surjective. -/
theorem transition_surjective {s t : Finset I} (h : s ≤ t) :
    Function.Surjective (transition R I r h) :=
  IsLocalization.Away.mapₐ_surjective_of_surjective _
    (FiniteRelationModel.transition_surjective R I h)

/-- Every localized quotient element occurs at every finite stage. -/
theorem toQuotient_surjective (s : Finset I) : Function.Surjective (toQuotient R I r s) :=
  IsLocalization.Away.mapₐ_surjective_of_surjective _
    (FiniteRelationModel.toQuotient_surjective R I s)

/-- Localized transitions compose. -/
theorem transition_comp {s t q : Finset I} (h : s ≤ t) (k : t ≤ q) :
    (transition R I r k).comp (transition R I r h) = transition R I r (h.trans k) := by
  apply IsLocalization.algHom_ext
    (Submonoid.powers (Ideal.Quotient.mk (FiniteRelationModel.relations I s) r))
  ext x
  change transition R I r k (transition R I r h (algebraMap _ (Stage I r s) x)) =
    transition R I r (h.trans k) (algebraMap _ (Stage I r s) x)
  rw [transition_algebraMap, transition_algebraMap, transition_algebraMap]
  exact congrArg (algebraMap _ (Stage I r q))
    (AlgHom.congr_fun (FiniteRelationModel.transition_comp R I h k) x)

/-- Localized projections form a compatible family. -/
theorem toQuotient_comp {s t : Finset I} (h : s ≤ t) :
    (toQuotient R I r t).comp (transition R I r h) = toQuotient R I r s := by
  apply IsLocalization.algHom_ext
    (Submonoid.powers (Ideal.Quotient.mk (FiniteRelationModel.relations I s) r))
  ext x
  change toQuotient R I r t (transition R I r h (algebraMap _ (Stage I r s) x)) =
    toQuotient R I r s (algebraMap _ (Stage I r s) x)
  rw [transition_algebraMap, toQuotient_algebraMap, toQuotient_algebraMap]
  exact congrArg (algebraMap _ (Quotient I r))
    (AlgHom.congr_fun (FiniteRelationModel.toQuotient_comp R I h) x)

end FLT.Mazur.FiniteRelationLocalization
