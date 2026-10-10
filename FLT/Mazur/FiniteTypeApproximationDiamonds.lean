/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeApproximationMaps

/-!
# Commutative diamonds of finite-type affine approximations

A commutative diamond of finite-type algebras has a commutative diamond of
finitely presented models. Its initial source stage is fixed, and all other
stages extend prescribed lower bounds. The limiting algebras need not be
finitely presented. This supplies the first compatibility squares in a
chart/intersection diagram; open immersion properties require localization.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R]
  {A : Type v} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
  {B : Type w} [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
  {C : Type z} [CommRing C] [Algebra R C] [Algebra.FiniteType R C]

/-- Two incoming arrows can be lifted while keeping both source stages fixed. -/
theorem exists_stageMap_pair_lift (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (a : Finset (relationIdeal R A)) (b : Finset (relationIdeal R B))
    (c : Finset (relationIdeal R C)) :
    ∃ q : Finset (relationIdeal R C), c ≤ q ∧
      ∃ (F : Stage R A a →ₐ[R] Stage R C q) (G : Stage R B b →ₐ[R] Stage R C q),
        (stageMap R C q).comp F = f.comp (stageMap R A a) ∧
        (stageMap R C q).comp G = g.comp (stageMap R B b) := by
  obtain ⟨t, hct, F, hF⟩ := exists_stageMap_lift f a c
  obtain ⟨q, htq, G, hG⟩ := exists_stageMap_lift g b t
  refine ⟨q, hct.trans htq,
    (FiniteRelationModel.transition R (relationIdeal R C) htq).comp F, G, ?_, hG⟩
  rw [← AlgHom.comp_assoc, stageMap_transition, hF]

/-- A commuting fork remains commuting at a sufficiently large target stage. -/
theorem exists_stageMap_fork_lift (f : B →ₐ[R] C) (g : A →ₐ[R] C)
    {T : Type*} [CommRing T] [Algebra R T] [Algebra.FiniteType R T]
    (a : Finset (relationIdeal R A)) (b : Finset (relationIdeal R B))
    (c : Finset (relationIdeal R C))
    (i : T →ₐ[R] Stage R B b) (j : T →ₐ[R] Stage R A a)
    (h : (f.comp (stageMap R B b)).comp i =
      (g.comp (stageMap R A a)).comp j) :
    ∃ q : Finset (relationIdeal R C), c ≤ q ∧
      ∃ (F : Stage R B b →ₐ[R] Stage R C q) (G : Stage R A a →ₐ[R] Stage R C q),
        (stageMap R C q).comp F = f.comp (stageMap R B b) ∧
        (stageMap R C q).comp G = g.comp (stageMap R A a) ∧ F.comp i = G.comp j := by
  obtain ⟨t, hct, F, G, hF, hG⟩ := exists_stageMap_pair_lift f g b a c
  have he : (FiniteRelationModel.toQuotient R (relationIdeal R C) t).comp (F.comp i) =
      (FiniteRelationModel.toQuotient R (relationIdeal R C) t).comp (G.comp j) := by
    apply AlgHom.ext
    intro x
    apply (quotientEquiv R C).injective
    change ((stageMap R C t).comp F) (i x) = ((stageMap R C t).comp G) (j x)
    rw [hF, hG]
    exact AlgHom.congr_fun h x
  obtain ⟨q, htq, hq⟩ := FiniteRelationModel.exists_transition_hom_eq
    (relationIdeal R C) t (F.comp i) (G.comp j) he
  let e := FiniteRelationModel.transition R (relationIdeal R C) htq
  refine ⟨q, hct.trans htq, e.comp F, e.comp G, ?_, ?_, ?_⟩
  · rw [← AlgHom.comp_assoc, stageMap_transition, hF]
  · rw [← AlgHom.comp_assoc, stageMap_transition, hG]
  · simpa only [AlgHom.comp_assoc] using hq

/-- A diamond of original algebras has a genuinely commutative finite-stage lift. -/
theorem exists_stageMap_diamond
    {D : Type*} [CommRing D] [Algebra R D] [Algebra.FiniteType R D]
    (f : A →ₐ[R] B) (g : A →ₐ[R] C) (h : B →ₐ[R] D) (k : C →ₐ[R] D)
    (comm : h.comp f = k.comp g)
    (a : Finset (relationIdeal R A)) (b : Finset (relationIdeal R B))
    (c : Finset (relationIdeal R C)) (d : Finset (relationIdeal R D)) :
    ∃ (b' : Finset (relationIdeal R B)) (c' : Finset (relationIdeal R C))
      (d' : Finset (relationIdeal R D)), b ≤ b' ∧ c ≤ c' ∧ d ≤ d' ∧
      ∃ (F : Stage R A a →ₐ[R] Stage R B b')
        (G : Stage R A a →ₐ[R] Stage R C c')
        (H : Stage R B b' →ₐ[R] Stage R D d')
        (K : Stage R C c' →ₐ[R] Stage R D d'),
        (stageMap R B b').comp F = f.comp (stageMap R A a) ∧
        (stageMap R C c').comp G = g.comp (stageMap R A a) ∧
        (stageMap R D d').comp H = h.comp (stageMap R B b') ∧
        (stageMap R D d').comp K = k.comp (stageMap R C c') ∧
        H.comp F = K.comp G := by
  obtain ⟨b', hbb, F, hF⟩ := exists_stageMap_lift f a b
  obtain ⟨c', hcc, G, hG⟩ := exists_stageMap_lift g a c
  have he : (h.comp (stageMap R B b')).comp F =
      (k.comp (stageMap R C c')).comp G := by
    rw [AlgHom.comp_assoc, AlgHom.comp_assoc, hF, hG,
      ← AlgHom.comp_assoc, ← AlgHom.comp_assoc, comm]
  obtain ⟨d', hdd, H, K, hH, hK, hcomm⟩ :=
    exists_stageMap_fork_lift h k c' b' d F G he
  exact ⟨b', c', d', hbb, hcc, hdd, F, G, H, K, hF, hG, hH, hK, hcomm⟩

end FLT.Mazur.FiniteTypeRelationModel
