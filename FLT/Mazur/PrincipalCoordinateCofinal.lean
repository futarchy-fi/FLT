/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalCoordinateDirected
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Cofinality of the two chart indices

The directed system of commuting lifts projects cofinally onto the relation
indices of both charts. Reindexing either chart by compatible coordinate
models therefore preserves its colimit ring and inverse-limit spectrum.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace FLT.Mazur.FiniteTypeRelationModel

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra.FiniteType R A] [Algebra.FiniteType R B]
  (a : A) (b : B) (f : Localization.Away a →ₐ[R] Localization.Away b)

/-- Forget a coordinate lift and retain its source relation set. -/
def principalSourceIndex : PrincipalMapStage a b f ⥤ Finset (relationIdeal R A) where
  obj x := x.source
  map h := homOfLE (leOfHom h).choose

/-- Forget a coordinate lift and retain its target relation set. -/
def principalTargetIndex : PrincipalMapStage a b f ⥤ Finset (relationIdeal R B) where
  obj x := x.target
  map h := homOfLE (leOfHom h).choose_spec.choose

/-- Every source relation stage is represented cofinally by compatible coordinate models. -/
instance principalSourceIndexFinal : (principalSourceIndex a b f).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro s
    obtain ⟨x, hx, _⟩ := exists_principalMapStage (a := a) (b := b) (f := f) s ∅
    exact ⟨x, ⟨homOfLE (by change s ≤ x.source; rw [hx])⟩⟩
  · intro s x i j
    exact ⟨x, 𝟙 x, Subsingleton.elim _ _⟩

/-- Every target relation stage is represented cofinally by compatible coordinate models. -/
instance principalTargetIndexFinal : (principalTargetIndex a b f).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro t
    obtain ⟨x, _, hx⟩ := exists_principalMapStage (a := a) (b := b) (f := f) ∅ t
    exact ⟨x, ⟨homOfLE hx⟩⟩
  · intro t x i j
    exact ⟨x, 𝟙 x, Subsingleton.elim _ _⟩

end FLT.Mazur.FiniteTypeRelationModel
