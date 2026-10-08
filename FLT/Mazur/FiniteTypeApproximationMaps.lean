/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeRelationPresentation
public import FLT.Mazur.FiniteRelationHomDescent
public import FLT.Mazur.FiniteRelationHomEquality

/-!
# Morphisms between finite-type affine approximations

A map between arbitrary finite-type algebras lifts from any fixed source
stage to a sufficiently large target stage. Two such lifts become equal
after enlarging the target. Neither original algebra is assumed finitely
presented over the base.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
  [Algebra.FiniteType R A] {B : Type w} [CommRing B] [Algebra R B]
  [Algebra.FiniteType R B]

/-- Any original map is realized on a fixed source stage after enlarging the target. -/
theorem exists_stageMap_lift (f : A →ₐ[R] B) (s : Finset (relationIdeal R A))
    (t : Finset (relationIdeal R B)) :
    ∃ (q : Finset (relationIdeal R B)), t ≤ q ∧
      ∃ g : Stage R A s →ₐ[R] Stage R B q,
        (stageMap R B q).comp g = f.comp (stageMap R A s) := by
  let φ := (quotientEquiv R B).symm.toAlgHom.comp (f.comp (stageMap R A s))
  obtain ⟨q, htq, g, hg⟩ :=
    FiniteRelationModel.exists_hom_lift (relationIdeal R B) t φ
  refine ⟨q, htq, g, ?_⟩
  apply AlgHom.ext
  intro x
  have h := congrArg (quotientEquiv R B) (AlgHom.congr_fun hg x)
  simpa only [stageMap, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    φ, AlgEquiv.apply_symm_apply] using h

/-- Two maps of models with the same original value agree at a later target stage. -/
theorem exists_stageMap_eq (s : Finset (relationIdeal R A))
    (t : Finset (relationIdeal R B)) (f g : Stage R A s →ₐ[R] Stage R B t)
    (h : (stageMap R B t).comp f = (stageMap R B t).comp g) :
    ∃ (q : Finset (relationIdeal R B)) (htq : t ≤ q),
      (FiniteRelationModel.transition R (relationIdeal R B) htq).comp f =
        (FiniteRelationModel.transition R (relationIdeal R B) htq).comp g := by
  apply FiniteRelationModel.exists_transition_hom_eq
  apply AlgHom.ext
  intro x
  apply (quotientEquiv R B).injective
  exact AlgHom.congr_fun h x

end FLT.Mazur.FiniteTypeRelationModel
