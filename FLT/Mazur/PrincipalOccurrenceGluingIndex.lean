/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceGluingStage
public import FLT.Mazur.PrincipalOccurrenceDirected
public import Mathlib.CategoryTheory.Filtered.Final
/-!
# Cofinal indexing by gluable occurrence stages

Cofinality in the existing occurrence order gives a filtered gluable
index and a final forgetful functor. The actual atlas supplies the
cofinality hypothesis in `FinitePrincipalAtlasGluingCofinal`.
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

variable [Finite ι] [∀ i, Finite (J i)]
  (hc : ∀ x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom),
    ∃ y : PrincipalOccurrenceGluingStage e, x ≤ y.val)

include hc

/-- A cofinal gluable subtype contains an actual stage. -/
theorem principalOccurrenceGluingStage_nonempty : Nonempty (PrincipalOccurrenceGluingStage e) := by
  obtain ⟨x⟩ := (inferInstance :
    Nonempty (PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom)))
  obtain ⟨y, _⟩ := hc x
  exact ⟨y⟩

/-- A common occurrence refinement can be refined once more to a gluable one. -/
theorem principalOccurrenceGluingStage_directed :
    IsDirectedOrder (PrincipalOccurrenceGluingStage e) where
  directed x y := by
    obtain ⟨z, hxz, hyz⟩ := exists_ge_ge x.val y.val
    obtain ⟨q, hzq⟩ := hc z
    exact ⟨q, hxz.trans hzq, hyz.trans hzq⟩

/-- Cofinal gluable stages form a filtered category. -/
theorem principalOccurrenceGluingStage_filtered :
    IsFiltered (PrincipalOccurrenceGluingStage e) := by
  let _ := principalOccurrenceGluingStage_nonempty e hc
  let _ := principalOccurrenceGluingStage_directed e hc
  infer_instance

/-- Forget the geometric membership proof while retaining all relations and coordinates. -/
def principalOccurrenceGluingIndex :
    PrincipalOccurrenceGluingStage e ⥤
      PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom) where
  obj x := x.val
  map h := homOfLE (leOfHom h)

/-- Restricting to these gluable stages preserves colimits of occurrence diagrams. -/
theorem principalOccurrenceGluingIndex_final : (principalOccurrenceGluingIndex e).Final := by
  let _ := principalOccurrenceGluingStage_filtered e hc
  apply Functor.final_of_exists_of_isFiltered
  · intro x
    obtain ⟨y, hxy⟩ := hc x
    exact ⟨y, ⟨homOfLE hxy⟩⟩
  · intro x y j k
    exact ⟨y, 𝟙 y, Subsingleton.elim _ _⟩

end FLT.Mazur.FiniteTypeRelationModel
