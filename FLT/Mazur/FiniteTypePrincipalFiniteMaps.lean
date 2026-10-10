/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalCoordinateStages
public import FLT.Mazur.FiniteRelationLocalizationCompatibleHomDescent

/-!
# Simultaneous maps into a principal-open model

Finite families of finitely presented sources lift to one stage. Finite
families of equations from finite-type sources hold at one later stage.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
  [Algebra.FiniteType R B] (b : B)

/-- Lift finitely many source maps into one principal-open stage. -/
theorem exists_principal_hom_lift_finite {ι : Type z} [Finite ι]
    (T : ι → Type w) [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)]
    [∀ i, Algebra.FinitePresentation R (T i)]
    (f : ∀ i, T i →ₐ[R] Localization.Away b) (s : Finset (relationIdeal R B)) :
    ∃ t : Finset (relationIdeal R B), s ≤ t ∧
      ∃ g : ∀ i, T i →ₐ[R] PrincipalStage R B b t,
        ∀ i, (principalStageMap R B b t).comp (g i) = f i := by
  let φ := fun i ↦ (principalQuotientEquiv R B b).symm.toAlgHom.comp (f i)
  obtain ⟨t, hst, g, hg⟩ := FiniteRelationLocalization.exists_hom_lift_finite
    (relationIdeal R B) (principalRepresentative R B b) T s φ
  refine ⟨t, hst, g, fun i ↦ ?_⟩
  apply AlgHom.ext
  intro x
  have h := congrArg (principalQuotientEquiv R B b) (AlgHom.congr_fun (hg i) x)
  simpa only [principalStageMap, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    φ, AlgEquiv.apply_symm_apply] using h

/-- Detect finitely many map equalities at a single principal-open stage. -/
theorem exists_principal_hom_eq_finite {ι : Type z} [Finite ι]
    (T : ι → Type w) [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)]
    [∀ i, Algebra.FiniteType R (T i)] (s : Finset (relationIdeal R B))
    (f g : ∀ i, T i →ₐ[R] PrincipalStage R B b s)
    (h : ∀ i, (principalStageMap R B b s).comp (f i) =
      (principalStageMap R B b s).comp (g i)) :
    ∃ (t : Finset (relationIdeal R B)) (hst : s ≤ t),
      ∀ i, (FiniteRelationLocalization.transition R (relationIdeal R B)
        (principalRepresentative R B b) hst).comp (f i) =
        (FiniteRelationLocalization.transition R (relationIdeal R B)
        (principalRepresentative R B b) hst).comp (g i) := by
  apply FiniteRelationLocalization.exists_transition_hom_eq_finite
  intro i
  apply AlgHom.ext
  intro x
  apply (principalQuotientEquiv R B b).injective
  exact AlgHom.congr_fun (h i) x

/-- Arbitrarily many finite source charts share a common target relation stage. -/
theorem exists_principalStageMap_finite_lift {ι : Type z} [Finite ι]
    (A : ι → Type w) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Algebra.FiniteType R (A i)] (a : ∀ i, A i)
    (f : ∀ i, Localization.Away (a i) →ₐ[R] Localization.Away b)
    (s : ∀ i, Finset (relationIdeal R (A i))) (t : Finset (relationIdeal R B)) :
    ∃ q : Finset (relationIdeal R B), t ≤ q ∧
      ∃ g : ∀ i, PrincipalStage R (A i) (a i) (s i) →ₐ[R] PrincipalStage R B b q,
        ∀ i, (principalStageMap R B b q).comp (g i) =
          (f i).comp (principalStageMap R (A i) (a i) (s i)) :=
  exists_principal_hom_lift_finite b _
    (fun i ↦ (f i).comp (principalStageMap R (A i) (a i) (s i))) t

end FLT.Mazur.FiniteTypeRelationModel
