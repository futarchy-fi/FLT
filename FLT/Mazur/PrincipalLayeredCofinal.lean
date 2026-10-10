/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalLayeredDirected

public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Cofinal projections of shared two-layer incidence models

Forgetting either incidence layer is cofinal. Thus every chart in either
layer is recovered over the same filtered index.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z v' w'

variable {R : Type u} [CommRing R]
  {ι : Type v} {κ : Type w} {τ : Type v'} {E : κ → Type z} {F : τ → Type w'}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {C : τ → Type u} [∀ k, CommRing (C k)] [∀ k, Algebra R (C k)]
  [∀ k, Algebra.FiniteType R (C k)]
  {src : ∀ j, E j → ι} {mid : ∀ k, F k → κ}
  {a : ∀ i, A i} {b : ∀ j, B j} {c : ∀ k, C k}
  {f : ∀ j e, Localization.Away (a (src j e)) →ₐ[R] Localization.Away (b j)}
  {g : ∀ k e, Localization.Away (b (mid k e)) →ₐ[R] Localization.Away (c k)}

/-- Forget the second layer while retaining the common middle stages. -/
def principalLayeredLowerIndex :
    PrincipalLayeredStage src mid a b c f g ⥤ PrincipalBipartiteStage src a b f where
  obj x := x.lower
  map h := homOfLE (leOfHom h).1

/-- Forget the first layer while retaining the common middle stages. -/
def principalLayeredUpperIndex :
    PrincipalLayeredStage src mid a b c f g ⥤ PrincipalBipartiteStage mid b c g where
  obj := principalLayeredUpper
  map h := homOfLE (leOfHom h).2

variable [∀ j, Finite (E j)] [∀ k, Finite (F k)]

/-- Every prescribed upper model admits a compatible lower layer after refinement. -/
theorem exists_principalLayeredStage_above_upper (y : PrincipalBipartiteStage mid b c g) :
    ∃ x : PrincipalLayeredStage src mid a b c f g, y ≤ principalLayeredUpper x := by
  obtain ⟨l, _, hl⟩ := exists_principalBipartiteStage (src := src) (a := a) (b := b)
    (f := f) (fun _ ↦ ∅) y.source
  obtain ⟨z, hz, ht⟩ := exists_principalBipartiteStage (src := mid) (a := b) (b := c)
    (f := g) l.target y.target
  have hs : y.source ≤ z.source := by rw [hz]; exact hl
  obtain ⟨w, hyw, _, hw⟩ := exists_principalBipartiteStage_compare y z hs ht
  refine ⟨principalLayeredOfLayers l w (hw.trans hz), ?_⟩
  rw [principalLayeredOfLayers_upper]
  exact hyw

/-- No lower incidence stage is lost by requiring a compatible second layer. -/
instance principalLayeredLowerIndexFinal :
    (principalLayeredLowerIndex (src := src) (mid := mid)
      (a := a) (b := b) (c := c) (f := f) (g := g)).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro l
    obtain ⟨x, hx, _⟩ := exists_principalLayeredStage_over (mid := mid) (c := c) (g := g)
      l (fun _ ↦ ∅)
    refine ⟨x, ⟨homOfLE ?_⟩⟩
    change l ≤ x.lower
    rw [hx]
  · intro l x j k
    exact ⟨x, 𝟙 x, Subsingleton.elim _ _⟩

/-- No upper incidence stage is lost by requiring a compatible first layer. -/
instance principalLayeredUpperIndexFinal :
    (principalLayeredUpperIndex (src := src) (mid := mid)
      (a := a) (b := b) (c := c) (f := f) (g := g)).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro y
    obtain ⟨x, hx⟩ := exists_principalLayeredStage_above_upper (src := src) (a := a) (f := f) y
    exact ⟨x, ⟨homOfLE hx⟩⟩
  · intro y x j k
    exact ⟨x, 𝟙 x, Subsingleton.elim _ _⟩

end FLT.Mazur.FiniteTypeRelationModel
