/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypePrincipalMaps

/-!
# Composition and inverse equations for principal coordinate models

Any chosen lifts of coordinate changes satisfy the original composition law
after enlarging the target. For inverse coordinate changes the round trip
becomes the transition map. These are eventual equations; a single pair of
mutually inverse finite-stage isomorphisms is not asserted.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R]
  {A : Type v} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
  {B : Type w} [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
  {C : Type z} [CommRing C] [Algebra R C] [Algebra.FiniteType R C]
  (a : A) (b : B) (c : C)

/-- Chosen lifts of a triple-overlap composition law agree at a later target. -/
theorem exists_principal_composition_eq
    (f : Localization.Away a →ₐ[R] Localization.Away b)
    (g : Localization.Away b →ₐ[R] Localization.Away c)
    (h : Localization.Away a →ₐ[R] Localization.Away c) (comm : g.comp f = h)
    (s : Finset (relationIdeal R A)) (t : Finset (relationIdeal R B))
    (q : Finset (relationIdeal R C))
    (F : PrincipalStage R A a s →ₐ[R] PrincipalStage R B b t)
    (G : PrincipalStage R B b t →ₐ[R] PrincipalStage R C c q)
    (H : PrincipalStage R A a s →ₐ[R] PrincipalStage R C c q)
    (hF : (principalStageMap R B b t).comp F = f.comp (principalStageMap R A a s))
    (hG : (principalStageMap R C c q).comp G = g.comp (principalStageMap R B b t))
    (hH : (principalStageMap R C c q).comp H = h.comp (principalStageMap R A a s)) :
    ∃ (q' : Finset (relationIdeal R C)) (hqq : q ≤ q'),
      (FiniteRelationLocalization.transition R (relationIdeal R C)
        (principalRepresentative R C c) hqq).comp (G.comp F) =
      (FiniteRelationLocalization.transition R (relationIdeal R C)
        (principalRepresentative R C c) hqq).comp H := by
  apply exists_principal_hom_eq
  rw [← AlgHom.comp_assoc, hG, AlgHom.comp_assoc, hF,
    ← AlgHom.comp_assoc, comm, hH]

/-- A lifted inverse round trip agrees with the source transition after refinement. -/
theorem exists_principal_inverse_eq
    (e : Localization.Away a ≃ₐ[R] Localization.Away b)
    (s s' : Finset (relationIdeal R A)) (hss : s ≤ s')
    (t : Finset (relationIdeal R B))
    (F : PrincipalStage R A a s →ₐ[R] PrincipalStage R B b t)
    (G : PrincipalStage R B b t →ₐ[R] PrincipalStage R A a s')
    (hF : (principalStageMap R B b t).comp F =
      e.toAlgHom.comp (principalStageMap R A a s))
    (hG : (principalStageMap R A a s').comp G =
      e.symm.toAlgHom.comp (principalStageMap R B b t)) :
    ∃ (q : Finset (relationIdeal R A)) (hsq : s' ≤ q),
      ((FiniteRelationLocalization.transition R (relationIdeal R A)
        (principalRepresentative R A a) hsq).comp G).comp F =
      FiniteRelationLocalization.transition R (relationIdeal R A)
        (principalRepresentative R A a) (hss.trans hsq) := by
  have he : (principalStageMap R A a s').comp (G.comp F) =
      (principalStageMap R A a s').comp
        (FiniteRelationLocalization.transition R (relationIdeal R A)
          (principalRepresentative R A a) hss) := by
    rw [principalStageMap_transition, ← AlgHom.comp_assoc, hG, AlgHom.comp_assoc, hF]
    ext x
    exact e.symm_apply_apply _
  obtain ⟨q, hsq, hq⟩ := exists_principal_hom_eq a s' (G.comp F) _ he
  refine ⟨q, hsq, ?_⟩
  rw [← AlgHom.comp_assoc, FiniteRelationLocalization.transition_comp] at hq
  simpa only [AlgHom.comp_assoc] using hq

end FLT.Mazur.FiniteTypeRelationModel
