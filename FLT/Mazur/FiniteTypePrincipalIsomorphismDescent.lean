/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypePrincipalSurjectiveLifts
public import FLT.Mazur.FiniteRelationLocalizationQuotientEquiv

/-!
# Genuine isomorphisms between finite principal-open models

An isomorphism of the original principal opens lifts to an isomorphism of
finite stages beyond any two prescribed bounds. The source and target remain
principal localizations of their original chart presentations.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
  [Algebra.FiniteType R A] (a : A)

/-- A finite quotient of a principal stage compatible with the original chart is a later stage. -/
theorem exists_principal_quotient_equiv {T : Type w} [CommRing T] [Algebra R T]
    [Algebra.FinitePresentation R T] (s : Finset (relationIdeal R A))
    (f : PrincipalStage R A a s →ₐ[R] T) (hf : Function.Surjective f)
    (h : RingHom.ker f.toRingHom ≤ RingHom.ker (principalStageMap R A a s).toRingHom) :
    ∃ (t : Finset (relationIdeal R A)) (hst : s ≤ t) (e : PrincipalStage R A a t ≃ₐ[R] T),
      e.toAlgHom.comp (FiniteRelationLocalization.transition R (relationIdeal R A)
        (principalRepresentative R A a) hst) = f := by
  refine FiniteRelationLocalization.exists_quotient_equiv
    (relationIdeal R A) (principalRepresentative R A a) s f hf ?_
  intro x hx
  apply (principalQuotientEquiv R A a).injective
  change principalStageMap R A a s x = principalQuotientEquiv R A a 0
  rw [map_zero]
  exact h hx

variable {B : Type z} [CommRing B] [Algebra R B] [Algebra.FiniteType R B] (b : B)

/-- A surjective coordinate lift of an original injection becomes an isomorphism. -/
theorem exists_principal_lift_equiv (f : Localization.Away a →ₐ[R] Localization.Away b)
    (hf : Function.Injective f) (s : Finset (relationIdeal R A))
    (t : Finset (relationIdeal R B))
    (g : PrincipalStage R A a s →ₐ[R] PrincipalStage R B b t) (hg : Function.Surjective g)
    (hfac : (principalStageMap R B b t).comp g = f.comp (principalStageMap R A a s)) :
    ∃ (q : Finset (relationIdeal R A)) (hsq : s ≤ q)
      (e : PrincipalStage R A a q ≃ₐ[R] PrincipalStage R B b t),
      e.toAlgHom.comp (FiniteRelationLocalization.transition R (relationIdeal R A)
        (principalRepresentative R A a) hsq) = g ∧
      (principalStageMap R B b t).comp e.toAlgHom = f.comp (principalStageMap R A a q) := by
  have hk : RingHom.ker g.toRingHom ≤ RingHom.ker (principalStageMap R A a s).toRingHom := by
    intro x hx
    change g x = 0 at hx
    apply hf
    change f (principalStageMap R A a s x) = f 0
    rw [← AlgHom.comp_apply, ← hfac, AlgHom.comp_apply, hx, map_zero, map_zero]
  obtain ⟨q, hsq, e, he⟩ := exists_principal_quotient_equiv a s g hg hk
  refine ⟨q, hsq, e, he, ?_⟩
  apply (AlgHom.cancel_right (FiniteRelationLocalization.transition_surjective R
    (relationIdeal R A) (principalRepresentative R A a) hsq)).mp
  rw [AlgHom.comp_assoc, he, hfac, AlgHom.comp_assoc, principalStageMap_transition]

/-- Isomorphisms of original principal opens occur as actual finite-stage isomorphisms. -/
theorem exists_principalStage_equiv (e : Localization.Away a ≃ₐ[R] Localization.Away b)
    (s : Finset (relationIdeal R A)) (t : Finset (relationIdeal R B)) :
    ∃ (q : Finset (relationIdeal R A)) (u : Finset (relationIdeal R B)), s ≤ q ∧ t ≤ u ∧
      ∃ d : PrincipalStage R A a q ≃ₐ[R] PrincipalStage R B b u,
        (principalStageMap R B b u).comp d.toAlgHom =
          e.toAlgHom.comp (principalStageMap R A a q) := by
  obtain ⟨u, htu, g, hg, hfac⟩ :=
    exists_principalStageMap_surjective_lift b a e.toAlgHom e.surjective s t
  obtain ⟨q, hsq, d, _, hd⟩ := exists_principal_lift_equiv a b e.toAlgHom e.injective s u g hg hfac
  exact ⟨q, u, hsq, htu, d, hd⟩

end FLT.Mazur.FiniteTypeRelationModel
