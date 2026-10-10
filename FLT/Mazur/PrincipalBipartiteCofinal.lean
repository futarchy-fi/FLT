/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalBipartiteDirected
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Cofinality of chart and overlap projections

Every original chart and overlap can use the same filtered incidence index.
No source stage is chosen independently for different occurrences of a chart.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {E : κ → Type z}
  [∀ j, Finite (E j)]
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  (src : ∀ j, E j → ι) (a : ∀ i, A i) (b : ∀ j, B j)
  (f : ∀ j e, Localization.Away (a (src j e)) →ₐ[R] Localization.Away (b j))

/-- Retain the shared relation set of one source chart. -/
def principalBipartiteSourceIndex (i : ι) :
    PrincipalBipartiteStage src a b f ⥤ Finset (relationIdeal R (A i)) where
  obj x := x.source i
  map h := homOfLE ((leOfHom h).1 i)

/-- Retain the relation set of one overlap target. -/
def principalBipartiteTargetIndex (j : κ) :
    PrincipalBipartiteStage src a b f ⥤ Finset (relationIdeal R (B j)) where
  obj x := x.target j
  map h := homOfLE (principalBipartite_target_mono (leOfHom h) j)

/-- Each chart projection is cofinal, including charts with no incidences. -/
instance principalBipartiteSourceIndexFinal (i : ι) :
    (principalBipartiteSourceIndex src a b f i).Final := by
  classical
  apply Functor.final_of_exists_of_isFiltered
  · intro s
    obtain ⟨x, hx, _⟩ := exists_principalBipartiteStage (src := src) (a := a) (b := b)
      (f := f) (Function.update (fun _ ↦ ∅) i s) (fun _ ↦ ∅)
    refine ⟨x, ⟨homOfLE ?_⟩⟩
    change s ≤ x.source i
    rw [hx, Function.update_self]
  · intro s x j k
    exact ⟨x, 𝟙 x, Subsingleton.elim _ _⟩

/-- Every overlap projection is cofinal in its own relation index. -/
instance principalBipartiteTargetIndexFinal (j : κ) :
    (principalBipartiteTargetIndex src a b f j).Final := by
  classical
  apply Functor.final_of_exists_of_isFiltered
  · intro t
    obtain ⟨x, _, hx⟩ := exists_principalBipartiteStage (src := src) (a := a) (b := b)
      (f := f) (fun _ ↦ ∅) (Function.update (fun _ ↦ ∅) j t)
    refine ⟨x, ⟨homOfLE ?_⟩⟩
    change t ≤ x.target j
    simpa only [Function.update_self] using hx j
  · intro t x i k
    exact ⟨x, 𝟙 x, Subsingleton.elim _ _⟩

end FLT.Mazur.FiniteTypeRelationModel
