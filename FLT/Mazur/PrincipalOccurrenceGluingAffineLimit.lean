/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceGluingIndex
public import FLT.Mazur.FiniteTypeAffineApproximation
public import Mathlib.CategoryTheory.Limits.Final
/-!
# Original affine charts as limits over gluable stages

Cofinality of gluable stages implies cofinality of every source-relation
index. Whiskering the established affine limit recovers each original chart.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))

/-- Read the finite source relations of one chart from a gluable stage. -/
def principalOccurrenceGluingSourceIndex (i : ι) :
    PrincipalOccurrenceGluingStage e ⥤ Finset (relationIdeal R (A i)) where
  obj x := x.val.source i
  map h := homOfLE (principalOccurrence_source_mono (leOfHom h) i)

variable [Finite ι] [∀ i, Finite (J i)]
  (hc : ∀ x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom),
    ∃ y : PrincipalOccurrenceGluingStage e, x ≤ y.val)

include hc in
/-- Every finite relation bound is reached by a gluable occurrence stage. -/
theorem principalOccurrenceGluingSourceIndex_final (i : ι) :
    (principalOccurrenceGluingSourceIndex e i).Final := by
  classical
  let _ := principalOccurrenceGluingStage_filtered e hc
  apply Functor.final_of_exists_of_isFiltered
  · intro s
    obtain ⟨x⟩ := (inferInstance :
      Nonempty (PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom)))
    obtain ⟨y, _hxy, hs, _ht⟩ := exists_principalOccurrenceStage_extension x
      (Function.update (fun _ ↦ ∅) i s) (fun _ ↦ ∅)
    obtain ⟨z, hyz⟩ := hc y
    refine ⟨z, ⟨homOfLE ?_⟩⟩
    have hsi : s ≤ y.source i := by simpa only [Function.update_self] using hs i
    exact hsi.trans (principalOccurrence_source_mono hyz i)
  · intro s x j k
    exact ⟨x, 𝟙 x, Subsingleton.elim _ _⟩

/-- The affine inverse diagram on one chart, indexed by the actual gluable stages. -/
def principalOccurrenceGluingAffineDiagram (i : ι) :
    (PrincipalOccurrenceGluingStage e)ᵒᵖ ⥤ Scheme.{u} :=
  (principalOccurrenceGluingSourceIndex e i).op ⋙ affineDiagram R (A i)

/-- The original affine chart gives the cone of its ambient projections. -/
def principalOccurrenceGluingAffineCone (i : ι) :
    Cone (principalOccurrenceGluingAffineDiagram e i) :=
  (affineCone R (A i)).whisker (principalOccurrenceGluingSourceIndex e i).op

/-- The original affine chart is the limit over all gluable occurrence stages. -/
def principalOccurrenceGluingAffineIsLimit (i : ι) :
    IsLimit (principalOccurrenceGluingAffineCone e i) := by
  let _ := principalOccurrenceGluingSourceIndex_final e hc i
  exact (Functor.Initial.isLimitWhiskerEquiv (principalOccurrenceGluingSourceIndex e i).op
    (affineCone R (A i))).symm (affineIsLimit R (A i))

end FLT.Mazur.FiniteTypeRelationModel
