/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Transporting an internal grading through a ring equivalence

The pulled-back homogeneous groups decompose the source ring. This construction
retains the specified ring equivalence on every homogeneous element.
-/

@[expose] public noncomputable section

open scoped DirectSum

namespace FLT.Mazur.RingEquivGrading

variable {A B σ : Type*} [CommRing A] [CommRing B] [SetLike σ B]
  [AddSubgroupClass σ B] (ℬ : ℕ → σ) [GradedRing ℬ] (e : A ≃+* B)

/-- Pull back each original homogeneous group along the given ring equivalence. -/
def grade (d : ℕ) : AddSubgroup A where
  carrier := {a | e a ∈ ℬ d}
  zero_mem' := by
    change e 0 ∈ ℬ d
    rw [map_zero]
    exact zero_mem _
  add_mem' := fun ha hb ↦ by
    change e (_ + _) ∈ ℬ d
    rw [map_add]
    exact add_mem ha hb
  neg_mem' := fun ha ↦ by
    change e (-_) ∈ ℬ d
    rw [map_neg]
    exact neg_mem ha

/-- The original equivalence restricts to each homogeneous group. -/
def component (d : ℕ) : grade ℬ e d ≃+ ℬ d where
  toFun a := ⟨e a, a.property⟩
  invFun b := ⟨e.symm b, by change e (e.symm b) ∈ ℬ d; simp⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a)
  right_inv b := Subtype.ext (e.apply_symm_apply b)
  map_add' a b := Subtype.ext (e.map_add a b)

/-- Recomposition commutes with the original equivalence. -/
theorem recompose_component (s : ⨁ d, grade ℬ e d) :
    e (DirectSum.coeAddMonoidHom (grade ℬ e) s) =
      DirectSum.coeAddMonoidHom ℬ (DirectSum.congrAddEquiv (component ℬ e) s) := by
  induction s using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of d s =>
    rw [DirectSum.coeAddMonoidHom_of]
    change e s = DirectSum.coeAddMonoidHom ℬ
      (DirectSum.map (fun d ↦ (component ℬ e d).toAddMonoidHom) (DirectSum.of _ d s))
    rw [DirectSum.map_of, DirectSum.coeAddMonoidHom_of]
    rfl
  | add s t hs ht => simp only [map_add, hs, ht]

/-- The pulled-back groups internally decompose the source ring. -/
theorem isInternal : DirectSum.IsInternal (grade ℬ e) := by
  have heq : (DirectSum.coeAddMonoidHom (grade ℬ e) : (⨁ d, grade ℬ e d) → A) =
      e.symm ∘ DirectSum.coeAddMonoidHom ℬ ∘ DirectSum.congrAddEquiv (component ℬ e) := by
    funext s
    exact e.injective (by simp only [Function.comp_apply, e.apply_symm_apply,
      recompose_component])
  rw [DirectSum.IsInternal, heq]
  exact e.symm.bijective.comp ((DirectSum.Decomposition.isInternal ℬ).comp
    (DirectSum.congrAddEquiv (component ℬ e)).bijective)

/-- Pulling back a grading through an equivalence gives the source its actual grading. -/
instance gradedRing : GradedRing (grade ℬ e) where
  toDecomposition := (isInternal ℬ e).chooseDecomposition _
  one_mem := by
    change e 1 ∈ ℬ 0
    rw [map_one]
    exact SetLike.GradedOne.one_mem
  mul_mem := by
    intro i j a b ha hb
    change e (a * b) ∈ ℬ (i + j)
    rw [map_mul]
    exact SetLike.GradedMul.mul_mem ha hb

end FLT.Mazur.RingEquivGrading
