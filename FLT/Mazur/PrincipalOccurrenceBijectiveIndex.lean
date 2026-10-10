/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceCofinalBijections
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# The directed index of bijective occurrence models

Restrict to the constructed bijective stages. Cofinality and directedness
follow by refining an arbitrary common occurrence stage once more.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  [Finite ι] [∀ i, Finite (J i)]
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))

variable [Finite κ]

/-- The actual finite occurrence stages whose coordinate maps are all bijective. -/
abbrev PrincipalOccurrenceBijectiveStage :=
  {x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom) //
    ∀ i k, Function.Bijective (x.hom i k)}

/-- The bijective index is cofinal in the full occurrence index. -/
theorem principalOccurrenceBijectiveStage_cofinal
    (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom)) :
    ∃ y : PrincipalOccurrenceBijectiveStage e, x ≤ y.val := by
  obtain ⟨y, hxy, _hs, _ht, hy⟩ :=
    exists_principalOccurrence_bijective_refinement e x x.source x.target
  exact ⟨⟨y, hy⟩, hxy⟩

instance principalOccurrenceBijectiveStageNonempty :
    Nonempty (PrincipalOccurrenceBijectiveStage e) := by
  obtain ⟨x, _hs, _ht, hx⟩ :=
    exists_principalOccurrence_bijective_stage e (fun _ ↦ ∅) (fun _ ↦ ∅)
  exact ⟨⟨x, hx⟩⟩

instance principalOccurrenceBijectiveStageDirected :
    IsDirectedOrder (PrincipalOccurrenceBijectiveStage e) where
  directed x y := by
    obtain ⟨z, hxz, hyz⟩ := exists_ge_ge x.val y.val
    obtain ⟨q, hzq⟩ := principalOccurrenceBijectiveStage_cofinal e z
    exact ⟨q, hxz.trans hzq, hyz.trans hzq⟩

/-- The bijective stages retain a filtered category for inverse-system constructions. -/
instance principalOccurrenceBijectiveStageFiltered :
    CategoryTheory.IsFiltered (PrincipalOccurrenceBijectiveStage e) := inferInstance

/-- Forget bijectivity without changing any finite relations or coordinates. -/
def principalOccurrenceBijectiveIndex :
    PrincipalOccurrenceBijectiveStage e ⥤
      PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom) where
  obj x := x.val
  map h := homOfLE (leOfHom h)

/-- Restricting diagrams to bijective occurrence models preserves their colimits. -/
instance principalOccurrenceBijectiveIndexFinal : (principalOccurrenceBijectiveIndex e).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro x
    obtain ⟨y, hxy⟩ := principalOccurrenceBijectiveStage_cofinal e x
    exact ⟨y, ⟨homOfLE hxy⟩⟩
  · intro x y j k
    exact ⟨y, 𝟙 y, Subsingleton.elim _ _⟩

end FLT.Mazur.FiniteTypeRelationModel
