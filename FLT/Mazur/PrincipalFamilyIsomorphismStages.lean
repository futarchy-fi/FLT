/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFamilyIsomorphismRefinement
public import FLT.Mazur.PrincipalFamilyCofinal

/-!
# A cofinal system of actual overlap isomorphisms

The stages whose coordinate maps are bijective form a nonempty directed
subsystem. Bijectivity need not survive arbitrary refinements; instead, every
common refinement is refined again using the proved isomorphism construction.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : Type u} [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
  (a : ∀ i, A i) (b : B) (e : ∀ i, Localization.Away (a i) ≃ₐ[R] Localization.Away b)

/-- The subsystem on which every incoming coordinate lift is an isomorphism. -/
def PrincipalFamilyIsomorphismStage :=
  {x : PrincipalFamilyStage a b (fun i ↦ (e i).toAlgHom) // ∀ i, Function.Bijective (x.hom i)}

/-- Isomorphism stages inherit commuting refinement from the full family index. -/
instance principalFamilyIsomorphismStagePreorder :
    Preorder (PrincipalFamilyIsomorphismStage a b e) :=
  inferInstanceAs (Preorder {x : PrincipalFamilyStage a b (fun i ↦ (e i).toAlgHom) //
    ∀ i, Function.Bijective (x.hom i)})

/-- Every coordinate family has an isomorphic refinement. -/
theorem exists_principalFamilyIsomorphismStage_above
    (x : PrincipalFamilyStage a b (fun i ↦ (e i).toAlgHom)) :
    ∃ y : PrincipalFamilyIsomorphismStage a b e, x ≤ y.val := by
  obtain ⟨y, hxy, hy⟩ := exists_principalFamily_bijective (fun i ↦ (e i).bijective) x
  exact ⟨⟨y, hy⟩, hxy⟩

/-- Actual isomorphism stages exist without assuming any finite presentation of the originals. -/
instance principalFamilyIsomorphismStageNonempty :
    Nonempty (PrincipalFamilyIsomorphismStage a b e) := by
  obtain ⟨x⟩ := principalFamilyStageNonempty (a := a) (b := b)
    (f := fun i ↦ (e i).toAlgHom)
  obtain ⟨y, _⟩ := exists_principalFamilyIsomorphismStage_above a b e x
  exact ⟨y⟩

/-- Any two actual overlap models have a common commuting isomorphism refinement. -/
instance principalFamilyIsomorphismStageDirected :
    IsDirectedOrder (PrincipalFamilyIsomorphismStage a b e) where
  directed x y := by
    obtain ⟨z, hxz, hyz⟩ := exists_ge_ge x.val y.val
    obtain ⟨t, hzt⟩ := exists_principalFamilyIsomorphismStage_above a b e z
    exact ⟨t, hxz.trans hzt, hyz.trans hzt⟩

/-- The isomorphism index is filtered. -/
instance principalFamilyIsomorphismStageFiltered :
    IsFiltered (PrincipalFamilyIsomorphismStage a b e) := inferInstance

/-- Forget bijectivity while retaining the same finite models and arrows. -/
def principalFamilyIsomorphismIndex :
    PrincipalFamilyIsomorphismStage a b e ⥤ PrincipalFamilyStage a b (fun i ↦ (e i).toAlgHom) where
  obj x := x.val
  map h := homOfLE (leOfHom h)

/-- Restricting to actual isomorphisms preserves all colimits of coordinate families. -/
instance principalFamilyIsomorphismIndexFinal : (principalFamilyIsomorphismIndex a b e).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro x
    obtain ⟨y, hxy⟩ := exists_principalFamilyIsomorphismStage_above a b e x
    exact ⟨y, ⟨homOfLE hxy⟩⟩
  · intro x y j k
    exact ⟨y, 𝟙 y, Subsingleton.elim _ _⟩

/-- Extract the genuine finite-stage equivalence from a constructed overlap model. -/
def principalFamilyStageEquiv (x : PrincipalFamilyIsomorphismStage a b e) (i : ι) :
    PrincipalStage R (A i) (a i) (x.val.source i) ≃ₐ[R] PrincipalStage R B b x.val.target :=
  AlgEquiv.ofBijective (x.val.hom i) (x.property i)

end FLT.Mazur.FiniteTypeRelationModel
