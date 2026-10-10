/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFamilyDirected
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Cofinal projections of the finite coordinate family index

The common filtered index is cofinal in all relation bounds simultaneously,
and in each individual chart index.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : Type u} [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
  (a : ∀ i, A i) (b : B)
  (f : ∀ i, Localization.Away (a i) →ₐ[R] Localization.Away b)

/-- Project to all source relation sets and the target relation set at once. -/
def principalFamilyBoundsIndex : PrincipalFamilyStage a b f ⥤
    (∀ i, Finset (relationIdeal R (A i))) × Finset (relationIdeal R B) where
  obj x := (x.source, x.target)
  map h := ⟨fun i ↦ homOfLE ((leOfHom h).choose i),
    homOfLE (leOfHom h).choose_spec.choose⟩

/-- All chart bounds can be reached simultaneously. -/
instance principalFamilyBoundsIndexFinal : (principalFamilyBoundsIndex a b f).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro s
    obtain ⟨x, hx, ht⟩ := exists_principalFamilyStage (a := a) (b := b) (f := f) s.1 s.2
    exact ⟨x, ⟨⟨fun i ↦ homOfLE (by change s.1 i ≤ x.source i; rw [hx]),
      homOfLE ht⟩⟩⟩
  · intro s x i j
    refine ⟨x, 𝟙 x, ?_⟩
    ext i <;> apply Subsingleton.elim

/-- Retain the relation set of one source chart. -/
def principalFamilySourceIndex (i : ι) :
    PrincipalFamilyStage a b f ⥤ Finset (relationIdeal R (A i)) where
  obj x := x.source i
  map h := homOfLE ((leOfHom h).choose i)

/-- Retain the common target relation set. -/
def principalFamilyTargetIndex :
    PrincipalFamilyStage a b f ⥤ Finset (relationIdeal R B) where
  obj x := x.target
  map h := homOfLE (leOfHom h).choose_spec.choose

/-- Each source chart is recovered over the family index. -/
instance principalFamilySourceIndexFinal (i : ι) :
    (principalFamilySourceIndex a b f i).Final := by
  classical
  apply Functor.final_of_exists_of_isFiltered
  · intro s
    obtain ⟨x, hx, _⟩ := exists_principalFamilyStage (a := a) (b := b) (f := f)
      (Function.update (fun _ ↦ ∅) i s) ∅
    refine ⟨x, ⟨homOfLE ?_⟩⟩
    change s ≤ x.source i
    rw [hx, Function.update_self]
  · intro s x j k
    exact ⟨x, 𝟙 x, Subsingleton.elim _ _⟩

/-- The overlap target is recovered over the same family index. -/
instance principalFamilyTargetIndexFinal : (principalFamilyTargetIndex a b f).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro t
    obtain ⟨x, _, hx⟩ := exists_principalFamilyStage (a := a) (b := b) (f := f) (fun _ ↦ ∅) t
    exact ⟨x, ⟨homOfLE hx⟩⟩
  · intro t x i j
    exact ⟨x, 𝟙 x, Subsingleton.elim _ _⟩

end FLT.Mazur.FiniteTypeRelationModel
