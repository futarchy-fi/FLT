/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypePrincipalMaps

/-!
# Commuting diagrams between principal-open models of different charts

Incoming maps from different charts lift to a common principal-open stage.
Equalities of their composites are imposed at a later target stage. In
particular, coordinate-change diamonds commute before passing to the limit.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R]
  {A : Type v} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
  {B : Type w} [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
  {C : Type z} [CommRing C] [Algebra R C] [Algebra.FiniteType R C]
  (a : A) (b : B) (c : C)

/-- Two different source charts can map into a common principal-open model. -/
theorem exists_principalStageMap_pair_lift
    (f : Localization.Away a →ₐ[R] Localization.Away c)
    (g : Localization.Away b →ₐ[R] Localization.Away c)
    (s : Finset (relationIdeal R A)) (t : Finset (relationIdeal R B))
    (q : Finset (relationIdeal R C)) :
    ∃ q' : Finset (relationIdeal R C), q ≤ q' ∧
      ∃ (F : PrincipalStage R A a s →ₐ[R] PrincipalStage R C c q')
        (G : PrincipalStage R B b t →ₐ[R] PrincipalStage R C c q'),
        (principalStageMap R C c q').comp F = f.comp (principalStageMap R A a s) ∧
        (principalStageMap R C c q').comp G = g.comp (principalStageMap R B b t) := by
  obtain ⟨v, hqv, F, hF⟩ := exists_principalStageMap_lift c a f s q
  obtain ⟨q', hvq, G, hG⟩ := exists_principalStageMap_lift c b g t v
  refine ⟨q', hqv.trans hvq,
    (FiniteRelationLocalization.transition R (relationIdeal R C)
      (principalRepresentative R C c) hvq).comp F, G, ?_, hG⟩
  rw [← AlgHom.comp_assoc, principalStageMap_transition, hF]

/-- A relation between two incoming arrows holds at a finite principal-open stage. -/
theorem exists_principalStageMap_fork_lift
    (f : Localization.Away a →ₐ[R] Localization.Away c)
    (g : Localization.Away b →ₐ[R] Localization.Away c)
    {T : Type*} [CommRing T] [Algebra R T] [Algebra.FiniteType R T]
    (s : Finset (relationIdeal R A)) (t : Finset (relationIdeal R B))
    (q : Finset (relationIdeal R C))
    (i : T →ₐ[R] PrincipalStage R A a s) (j : T →ₐ[R] PrincipalStage R B b t)
    (h : (f.comp (principalStageMap R A a s)).comp i =
      (g.comp (principalStageMap R B b t)).comp j) :
    ∃ q' : Finset (relationIdeal R C), q ≤ q' ∧
      ∃ (F : PrincipalStage R A a s →ₐ[R] PrincipalStage R C c q')
        (G : PrincipalStage R B b t →ₐ[R] PrincipalStage R C c q'),
        (principalStageMap R C c q').comp F = f.comp (principalStageMap R A a s) ∧
        (principalStageMap R C c q').comp G = g.comp (principalStageMap R B b t) ∧
        F.comp i = G.comp j := by
  obtain ⟨v, hqv, F, G, hF, hG⟩ := exists_principalStageMap_pair_lift a b c f g s t q
  have he : (principalStageMap R C c v).comp (F.comp i) =
      (principalStageMap R C c v).comp (G.comp j) := by
    rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, hF, hG, h]
  obtain ⟨q', hvq, heq⟩ := exists_principal_hom_eq c v (F.comp i) (G.comp j) he
  let e := FiniteRelationLocalization.transition R (relationIdeal R C)
    (principalRepresentative R C c) hvq
  refine ⟨q', hqv.trans hvq, e.comp F, e.comp G, ?_, ?_, ?_⟩
  · rw [← AlgHom.comp_assoc, principalStageMap_transition, hF]
  · rw [← AlgHom.comp_assoc, principalStageMap_transition, hG]
  · simpa only [AlgHom.comp_assoc] using heq

/-- A coordinate-change diamond descends to genuinely commuting finite models. -/
theorem exists_principalStageMap_diamond
    {D : Type*} [CommRing D] [Algebra R D] [Algebra.FiniteType R D] (d : D)
    (f : Localization.Away a →ₐ[R] Localization.Away b)
    (g : Localization.Away a →ₐ[R] Localization.Away c)
    (h : Localization.Away b →ₐ[R] Localization.Away d)
    (k : Localization.Away c →ₐ[R] Localization.Away d) (comm : h.comp f = k.comp g)
    (s : Finset (relationIdeal R A)) (t : Finset (relationIdeal R B))
    (q : Finset (relationIdeal R C)) (v : Finset (relationIdeal R D)) :
    ∃ (t' : Finset (relationIdeal R B)) (q' : Finset (relationIdeal R C))
      (v' : Finset (relationIdeal R D)), t ≤ t' ∧ q ≤ q' ∧ v ≤ v' ∧
      ∃ (F : PrincipalStage R A a s →ₐ[R] PrincipalStage R B b t')
        (G : PrincipalStage R A a s →ₐ[R] PrincipalStage R C c q')
        (H : PrincipalStage R B b t' →ₐ[R] PrincipalStage R D d v')
        (K : PrincipalStage R C c q' →ₐ[R] PrincipalStage R D d v'),
        (principalStageMap R B b t').comp F = f.comp (principalStageMap R A a s) ∧
        (principalStageMap R C c q').comp G = g.comp (principalStageMap R A a s) ∧
        (principalStageMap R D d v').comp H = h.comp (principalStageMap R B b t') ∧
        (principalStageMap R D d v').comp K = k.comp (principalStageMap R C c q') ∧
        H.comp F = K.comp G := by
  obtain ⟨t', htt, F, hF⟩ := exists_principalStageMap_lift b a f s t
  obtain ⟨q', hqq, G, hG⟩ := exists_principalStageMap_lift c a g s q
  have he : (h.comp (principalStageMap R B b t')).comp F =
      (k.comp (principalStageMap R C c q')).comp G := by
    rw [AlgHom.comp_assoc, AlgHom.comp_assoc, hF, hG,
      ← AlgHom.comp_assoc, ← AlgHom.comp_assoc, comm]
  obtain ⟨v', hvv, H, K, hH, hK, hcomm⟩ :=
    exists_principalStageMap_fork_lift b c d h k t' q' v F G he
  exact ⟨t', q', v', htt, hqq, hvv, F, G, H, K, hF, hG, hH, hK, hcomm⟩

end FLT.Mazur.FiniteTypeRelationModel
