/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFamilyRelations
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# A cofinal subsystem satisfying prescribed finite equations

Equations on finitely many finite-type test algebras persist under commuting
refinement. If they hold in the original overlap ring, the stages satisfying
them form a directed cofinal subsystem of all incoming coordinate families.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : Type u} [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
  {a : ∀ i, A i} {b : B}
  {f : ∀ i, Localization.Away (a i) →ₐ[R] Localization.Away b}
  {κ : Type w} {C : κ → Type z} [∀ k, CommRing (C k)] [∀ k, Algebra R (C k)]
  (x : PrincipalFamilyStage a b f)
  (g h : ∀ k, C k →ₐ[R] PrincipalStage R B b x.target)

/-- A refinement of `x` on which all prescribed equations hold. -/
def PrincipalFamilyEquations (y : PrincipalFamilyStage a b f) : Prop :=
  x ≤ y ∧ ∃ ht : x.target ≤ y.target, ∀ k,
    (principalTransition b ht).comp (g k) = (principalTransition b ht).comp (h k)

/-- Equations remain true under every commuting refinement. -/
theorem principalFamilyEquations_mono {y z : PrincipalFamilyStage a b f}
    (hy : PrincipalFamilyEquations x g h y) (hyz : y ≤ z) :
    PrincipalFamilyEquations x g h z := by
  obtain ⟨hxy, ht, he⟩ := hy
  refine ⟨hxy.trans hyz, ht.trans hyz.choose_spec.choose, fun k ↦ ?_⟩
  calc
    (principalTransition b (ht.trans hyz.choose_spec.choose)).comp (g k) =
        (principalTransition b hyz.choose_spec.choose).comp
          ((principalTransition b ht).comp (g k)) := by
      rw [← AlgHom.comp_assoc, principalTransition_comp]
    _ = (principalTransition b hyz.choose_spec.choose).comp
        ((principalTransition b ht).comp (h k)) := by rw [he k]
    _ = (principalTransition b (ht.trans hyz.choose_spec.choose)).comp (h k) := by
      rw [← AlgHom.comp_assoc, principalTransition_comp]

/-- The subsystem cut out by finite equations, with its inherited refinement order. -/
def PrincipalFamilyEquationStage :=
  {y : PrincipalFamilyStage a b f // PrincipalFamilyEquations x g h y}

/-- Refinement on the equation subsystem is inherited from the family index. -/
instance principalFamilyEquationStagePreorder :
    Preorder (PrincipalFamilyEquationStage x g h) :=
  inferInstanceAs (Preorder {y // PrincipalFamilyEquations x g h y})

/-- Forget the equations and retain the underlying simultaneous coordinate lift. -/
def principalFamilyEquationIndex :
    PrincipalFamilyEquationStage x g h ⥤ PrincipalFamilyStage a b f where
  obj y := y.val
  map e := homOfLE (leOfHom e)

variable [Finite κ] [∀ k, Algebra.FiniteType R (C k)]

/-- Equations true in the original overlap ring hold at some finite refinement. -/
theorem exists_principalFamilyEquations
    (he : ∀ k, (principalStageMap R B b x.target).comp (g k) =
      (principalStageMap R B b x.target).comp (h k)) :
    ∃ y, PrincipalFamilyEquations x g h y := by
  obtain ⟨t, ht, hcomm⟩ := exists_principal_hom_eq_finite b C x.target g h he
  exact ⟨principalFamilyTargetExtension x t ht,
    principalFamilyTargetExtension_le x t ht, ht, hcomm⟩

variable [Finite ι]

omit [Finite κ] [∀ k, Algebra.FiniteType R (C k)] in
/-- Common family refinements preserve the chosen equations. -/
instance principalFamilyEquationStageDirected :
    IsDirectedOrder (PrincipalFamilyEquationStage x g h) where
  directed y z := by
    obtain ⟨t, hyt, hzt⟩ := exists_ge_ge y.val z.val
    exact ⟨⟨t, principalFamilyEquations_mono x g h y.property hyt⟩, hyt, hzt⟩

/-- One can satisfy the equations beyond any preassigned family stage. -/
theorem exists_principalFamilyEquations_above
    (he : ∀ k, (principalStageMap R B b x.target).comp (g k) =
      (principalStageMap R B b x.target).comp (h k)) (y : PrincipalFamilyStage a b f) :
    ∃ z, y ≤ z ∧ PrincipalFamilyEquations x g h z := by
  obtain ⟨t, ht⟩ := exists_principalFamilyEquations x g h he
  obtain ⟨z, hyz, htz⟩ := exists_ge_ge y t
  exact ⟨z, hyz, principalFamilyEquations_mono x g h ht htz⟩

/-- Imposing the finite equations does not change any colimit on the family index. -/
theorem principalFamilyEquationIndex_final
    (he : ∀ k, (principalStageMap R B b x.target).comp (g k) =
      (principalStageMap R B b x.target).comp (h k)) :
    (principalFamilyEquationIndex x g h).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro y
    obtain ⟨z, hyz, hz⟩ := exists_principalFamilyEquations_above x g h he y
    exact ⟨⟨z, hz⟩, ⟨homOfLE hyz⟩⟩
  · intro y z j k
    exact ⟨z, 𝟙 z, Subsingleton.elim _ _⟩

end FLT.Mazur.FiniteTypeRelationModel
