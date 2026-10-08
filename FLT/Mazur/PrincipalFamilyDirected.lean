/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFamilyStages
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Directed refinement of simultaneous coordinate lifts

Finite equality detection imposes all refinement squares at once. The
source family and the common target can extend arbitrary relation bounds.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : Type u} [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
  {a : ∀ i, A i} {b : B}
  {f : ∀ i, Localization.Away (a i) →ₐ[R] Localization.Away b}

/-- Impose all squares against an old family by enlarging only the target. -/
theorem exists_principalFamilyStage_compare (x z : PrincipalFamilyStage a b f)
    (hs : x.source ≤ z.source) (ht : x.target ≤ z.target) :
    ∃ w : PrincipalFamilyStage a b f, x ≤ w ∧ z ≤ w ∧ w.source = z.source := by
  have he (i) : (principalStageMap R B b z.target).comp
        ((z.hom i).comp (principalTransition (a i) (hs i))) =
      (principalStageMap R B b z.target).comp
        ((principalTransition b ht).comp (x.hom i)) := by
    rw [← AlgHom.comp_assoc, z.fac, AlgHom.comp_assoc, principalStageMap_transition,
      ← AlgHom.comp_assoc, principalStageMap_transition, x.fac]
  obtain ⟨q, hq, hcomm⟩ := exists_principal_hom_eq_finite b
    (fun i ↦ PrincipalStage R (A i) (a i) (x.source i)) z.target
    (fun i ↦ (z.hom i).comp (principalTransition (a i) (hs i)))
    (fun i ↦ (principalTransition b ht).comp (x.hom i)) he
  let w : PrincipalFamilyStage a b f :=
    { source := z.source
      target := q
      hom := fun i ↦ (principalTransition b hq).comp (z.hom i)
      fac := fun i ↦ by rw [← AlgHom.comp_assoc, principalStageMap_transition, z.fac] }
  refine ⟨w, ⟨hs, ht.trans hq, fun i ↦ ?_⟩, ⟨le_rfl, hq, fun i ↦ ?_⟩, rfl⟩
  · change ((principalTransition b hq).comp (z.hom i)).comp
        (principalTransition (a i) (hs i)) = _
    rw [AlgHom.comp_assoc, hcomm, ← AlgHom.comp_assoc, principalTransition_comp]
  · change ((principalTransition b hq).comp (z.hom i)).comp
        (principalTransition (a i) (le_refl (z.source i))) = _
    rw [principalTransition_refl, AlgHom.comp_id]

/-- Extend a family past arbitrary source and target relation bounds. -/
theorem exists_principalFamilyStage_extension (x : PrincipalFamilyStage a b f)
    (s : ∀ i, Finset (relationIdeal R (A i))) (t : Finset (relationIdeal R B)) :
    ∃ w : PrincipalFamilyStage a b f, x ≤ w ∧ s ≤ w.source ∧ t ≤ w.target := by
  classical
  obtain ⟨z, hzS, hzT⟩ := exists_principalFamilyStage (a := a) (b := b) (f := f)
    (fun i ↦ x.source i ∪ s i) (x.target ∪ t)
  have hxs : x.source ≤ z.source := by
    rw [hzS]
    exact fun _ ↦ Finset.subset_union_left
  have hxt : x.target ≤ z.target := Finset.subset_union_left.trans hzT
  obtain ⟨w, hxw, hzw, hw⟩ := exists_principalFamilyStage_compare x z hxs hxt
  refine ⟨w, hxw, ?_, ?_⟩
  · rw [hw, hzS]
    exact fun _ ↦ Finset.subset_union_right
  · exact Finset.subset_union_right.trans (hzT.trans hzw.choose_spec.choose)

/-- Any two simultaneous coordinate lifts have a common commuting refinement. -/
instance principalFamilyStageDirected : IsDirectedOrder (PrincipalFamilyStage a b f) where
  directed x y := by
    obtain ⟨z, hxz, hyS, hyT⟩ := exists_principalFamilyStage_extension x y.source y.target
    obtain ⟨w, hyw, hzw, _⟩ := exists_principalFamilyStage_compare y z hyS hyT
    exact ⟨w, hxz.trans hzw, hyw⟩

/-- The category of finite incoming coordinate families is filtered. -/
instance principalFamilyStageFiltered :
    CategoryTheory.IsFiltered (PrincipalFamilyStage a b f) := inferInstance

end FLT.Mazur.FiniteTypeRelationModel
