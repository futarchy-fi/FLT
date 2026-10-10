/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFanIsomorphismRefinement
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# A cofinal system of shared-chart isomorphism fans

Actual isomorphisms on distinct principal opens form a filtered system with
one ambient source stage. Its projections are cofinal in the ambient chart
and in every separate target chart.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.FiniteType R A] {ι : Type v} [Finite ι]
  {B : ι → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
  [∀ i, Algebra.FiniteType R (B i)]
  (a : ι → A) (b : ∀ i, B i)
  (e : ∀ i, Localization.Away (a i) ≃ₐ[R] Localization.Away (b i))

/-- Fan stages whose coordinate maps are all actual isomorphisms. -/
def PrincipalFanIsomorphismStage :=
  {x : PrincipalFanStage a b (fun i ↦ (e i).toAlgHom) // ∀ i, Function.Bijective (x.hom i)}

/-- Isomorphism fans inherit commuting refinement. -/
instance principalFanIsomorphismStagePreorder : Preorder (PrincipalFanIsomorphismStage a b e) :=
  inferInstanceAs (Preorder {x : PrincipalFanStage a b (fun i ↦ (e i).toAlgHom) //
    ∀ i, Function.Bijective (x.hom i)})

/-- Every finite fan has a commuting isomorphism refinement with a shared source. -/
theorem exists_principalFanIsomorphismStage_above
    (x : PrincipalFanStage a b (fun i ↦ (e i).toAlgHom)) :
    ∃ y : PrincipalFanIsomorphismStage a b e, x ≤ y.val := by
  obtain ⟨y, hxy, hy⟩ := exists_principalFan_bijective e x
  exact ⟨⟨y, hy⟩, hxy⟩

/-- There is an actual isomorphism fan without finite presentation of the original charts. -/
instance principalFanIsomorphismStageNonempty : Nonempty (PrincipalFanIsomorphismStage a b e) := by
  obtain ⟨x⟩ := principalFanStageNonempty (a := a) (b := b) (f := fun i ↦ (e i).toAlgHom)
  obtain ⟨y, _⟩ := exists_principalFanIsomorphismStage_above a b e x
  exact ⟨y⟩

/-- A common refinement can itself be refined to restore all isomorphisms. -/
instance principalFanIsomorphismStageDirected :
    IsDirectedOrder (PrincipalFanIsomorphismStage a b e) where
  directed x y := by
    obtain ⟨z, hxz, hyz⟩ := exists_ge_ge x.val y.val
    obtain ⟨w, hzw⟩ := exists_principalFanIsomorphismStage_above a b e z
    exact ⟨w, hxz.trans hzw, hyz.trans hzw⟩

/-- The shared-chart isomorphism system is filtered. -/
instance principalFanIsomorphismStageFiltered : IsFiltered (PrincipalFanIsomorphismStage a b e) :=
  inferInstance

/-- Forget bijectivity while preserving the common ambient chart and all arrows. -/
def principalFanIsomorphismIndex :
    PrincipalFanIsomorphismStage a b e ⥤ PrincipalFanStage a b (fun i ↦ (e i).toAlgHom) where
  obj x := x.val
  map h := homOfLE (leOfHom h)

/-- Isomorphism fans are cofinal among all shared-chart fans. -/
instance principalFanIsomorphismIndexFinal : (principalFanIsomorphismIndex a b e).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro x
    obtain ⟨y, hxy⟩ := exists_principalFanIsomorphismStage_above a b e x
    exact ⟨y, ⟨homOfLE hxy⟩⟩
  · intro x y j k
    exact ⟨y, 𝟙 y, Subsingleton.elim _ _⟩

/-- The common ambient relation set of an isomorphism fan. -/
def principalIsoFanSourceIndex :
    PrincipalFanIsomorphismStage a b e ⥤ Finset (relationIdeal R A) where
  obj x := x.val.source
  map h := homOfLE (leOfHom h).1

/-- The relation set at one target of an isomorphism fan. -/
def principalIsoFanTargetIndex (i : ι) :
    PrincipalFanIsomorphismStage a b e ⥤ Finset (relationIdeal R (B i)) where
  obj x := x.val.target i
  map h := homOfLE (principalFan_target_mono (leOfHom h) i)

/-- The common chart index remains cofinal after imposing all isomorphisms. -/
instance principalIsoFanSourceIndexFinal : (principalIsoFanSourceIndex a b e).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro s
    obtain ⟨x, hx, _⟩ := exists_principalFanStage (a := a) (b := b)
      (f := fun i ↦ (e i).toAlgHom) s (fun _ ↦ ∅)
    obtain ⟨y, hxy⟩ := exists_principalFanIsomorphismStage_above a b e x
    exact ⟨y, ⟨homOfLE (hx ▸ hxy.1)⟩⟩
  · intro x y j k
    exact ⟨y, 𝟙 y, Subsingleton.elim _ _⟩

/-- Each target chart index is cofinal on the same isomorphism system. -/
instance principalIsoFanTargetIndexFinal (i : ι) : (principalIsoFanTargetIndex a b e i).Final := by
  classical
  apply Functor.final_of_exists_of_isFiltered
  · intro t
    obtain ⟨x, _, hx⟩ := exists_principalFanStage (a := a) (b := b)
      (f := fun i ↦ (e i).toAlgHom) ∅ (Function.update (fun _ ↦ ∅) i t)
    obtain ⟨y, hxy⟩ := exists_principalFanIsomorphismStage_above a b e x
    refine ⟨y, ⟨homOfLE ?_⟩⟩
    change t ≤ y.val.target i
    have ht := (hx i).trans (principalFan_target_mono hxy i)
    simpa only [Function.update_self] using ht
  · intro x y j k
    exact ⟨y, 𝟙 y, Subsingleton.elim _ _⟩

/-- Extract the constructed coordinate equivalence on each principal open. -/
def principalFanStageEquiv (x : PrincipalFanIsomorphismStage a b e) (i : ι) :
    PrincipalStage R A (a i) x.val.source ≃ₐ[R] PrincipalStage R (B i) (b i) (x.val.target i) :=
  AlgEquiv.ofBijective (x.val.hom i) (x.property i)

end FLT.Mazur.FiniteTypeRelationModel
