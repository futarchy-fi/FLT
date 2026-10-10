/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypePrincipalPresentation
public import FLT.Mazur.FiniteRelationLocalizationHomDescent
public import FLT.Mazur.FiniteRelationLocalizationHomEquality

/-!
# Maps between principal-open approximations of different charts

Transport localized descent through the presentation equivalence. The source
stage is fixed, the target can be required to extend any specified stage, and
the original affine charts need only be finite type over the base.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
  [Algebra.FiniteType R B] (b : B)

/-- A finitely presented source maps into a finite principal-open model. -/
theorem exists_principal_hom_lift {T : Type w} [CommRing T] [Algebra R T]
    [Algebra.FinitePresentation R T] (f : T →ₐ[R] Localization.Away b)
    (s : Finset (relationIdeal R B)) :
    ∃ t : Finset (relationIdeal R B), s ≤ t ∧
      ∃ g : T →ₐ[R] PrincipalStage R B b t, (principalStageMap R B b t).comp g = f := by
  let φ := (principalQuotientEquiv R B b).symm.toAlgHom.comp f
  obtain ⟨t, hst, g, hg⟩ := FiniteRelationLocalization.exists_hom_lift
    (relationIdeal R B) (principalRepresentative R B b) s φ
  refine ⟨t, hst, g, ?_⟩
  apply AlgHom.ext
  intro x
  have h := congrArg (principalQuotientEquiv R B b) (AlgHom.congr_fun hg x)
  simpa only [principalStageMap, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    φ, AlgEquiv.apply_symm_apply] using h

/-- Equality from a finite-type source holds after enlarging the principal stage. -/
theorem exists_principal_hom_eq {T : Type w} [CommRing T] [Algebra R T]
    [Algebra.FiniteType R T] (s : Finset (relationIdeal R B))
    (f g : T →ₐ[R] PrincipalStage R B b s)
    (h : (principalStageMap R B b s).comp f = (principalStageMap R B b s).comp g) :
    ∃ (t : Finset (relationIdeal R B)) (hst : s ≤ t),
      (FiniteRelationLocalization.transition R (relationIdeal R B)
        (principalRepresentative R B b) hst).comp f =
      (FiniteRelationLocalization.transition R (relationIdeal R B)
        (principalRepresentative R B b) hst).comp g := by
  apply FiniteRelationLocalization.exists_transition_hom_eq
  apply AlgHom.ext
  intro x
  apply (principalQuotientEquiv R B b).injective
  exact AlgHom.congr_fun h x

variable {A : Type z} [CommRing A] [Algebra R A] [Algebra.FiniteType R A] (a : A)

/-- Coordinate changes between different charts descend from any fixed source stage. -/
theorem exists_principalStageMap_lift
    (f : Localization.Away a →ₐ[R] Localization.Away b)
    (s : Finset (relationIdeal R A)) (t : Finset (relationIdeal R B)) :
    ∃ q : Finset (relationIdeal R B), t ≤ q ∧
      ∃ g : PrincipalStage R A a s →ₐ[R] PrincipalStage R B b q,
        (principalStageMap R B b q).comp g = f.comp (principalStageMap R A a s) :=
  exists_principal_hom_lift b (f.comp (principalStageMap R A a s)) t

end FLT.Mazur.FiniteTypeRelationModel
