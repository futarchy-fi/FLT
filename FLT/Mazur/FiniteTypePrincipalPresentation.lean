/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeRelationPresentation
public import FLT.Mazur.FiniteRelationLocalizationStages

/-!
# Principal-open models for arbitrary finite-type algebras

Lift a denominator to the chosen polynomial presentation, and identify the
localized full quotient with the original principal-open algebra. This keeps
the relation index of the ambient chart and assumes no finite presentation
of the original algebra.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v

variable (R : Type u) [CommRing R] (B : Type v) [CommRing B] [Algebra R B]
  [Algebra.FiniteType R B]

/-- A polynomial representative of a denominator on the original chart. -/
def principalRepresentative (b : B) : MvPolynomial (Fin (numGenerators R B)) R :=
  (presentationMap_surjective R B b).choose

/-- The chosen polynomial evaluates to the requested denominator. -/
@[simp] theorem principalRepresentative_spec (b : B) :
    presentationMap R B (principalRepresentative R B b) = b :=
  (presentationMap_surjective R B b).choose_spec

/-- A principal-open model over the same relation index as the ambient affine model. -/
abbrev PrincipalStage (b : B) (s : Finset (relationIdeal R B)) :=
  FiniteRelationLocalization.Stage (relationIdeal R B) (principalRepresentative R B b) s

/-- Each principal-open model is finitely presented over the original base. -/
instance principalStage_finitePresentation (b : B) (s : Finset (relationIdeal R B)) :
    Algebra.FinitePresentation R (PrincipalStage R B b s) := inferInstance

/-- Recover the original principal-open algebra from its localized presentation. -/
def principalQuotientEquiv (b : B) :
    FiniteRelationLocalization.Quotient (relationIdeal R B) (principalRepresentative R B b) ≃ₐ[R]
      Localization.Away b :=
  IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers (Ideal.Quotient.mk (relationIdeal R B)
      (principalRepresentative R B b))) (T := Submonoid.powers b)
    _ _ (quotientEquiv R B) (by
    rw [Submonoid.map_powers]
    congr 1
    exact principalRepresentative_spec R B b)

/-- Projection from a principal-open model to the original principal-open algebra. -/
def principalStageMap (b : B) (s : Finset (relationIdeal R B)) :
    PrincipalStage R B b s →ₐ[R] Localization.Away b :=
  (principalQuotientEquiv R B b).toAlgHom.comp
    (FiniteRelationLocalization.toQuotient R (relationIdeal R B)
      (principalRepresentative R B b) s)

/-- The projection agrees with the ambient chart map on every numerator. -/
@[simp] theorem principalStageMap_algebraMap (b : B) (s : Finset (relationIdeal R B))
    (x : Stage R B s) :
    principalStageMap R B b s (algebraMap _ (PrincipalStage R B b s) x) =
      algebraMap B (Localization.Away b) (stageMap R B s x) := by
  rw [principalStageMap, AlgHom.comp_apply, FiniteRelationLocalization.toQuotient_algebraMap]
  unfold principalQuotientEquiv
  exact IsLocalization.algEquivOfAlgEquiv_eq _ _

/-- Principal-open projections are surjective on rings. -/
theorem principalStageMap_surjective (b : B) (s : Finset (relationIdeal R B)) :
    Function.Surjective (principalStageMap R B b s) :=
  (principalQuotientEquiv R B b).surjective.comp
    (FiniteRelationLocalization.toQuotient_surjective R (relationIdeal R B)
      (principalRepresentative R B b) s)

/-- Principal-open projections commute with the ambient model transitions. -/
theorem principalStageMap_transition (b : B) {s t : Finset (relationIdeal R B)} (h : s ≤ t) :
    (principalStageMap R B b t).comp
      (FiniteRelationLocalization.transition R (relationIdeal R B)
        (principalRepresentative R B b) h) = principalStageMap R B b s := by
  rw [principalStageMap, AlgHom.comp_assoc, FiniteRelationLocalization.toQuotient_comp]
  rfl

end FLT.Mazur.FiniteTypeRelationModel
