/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveLineCharts
public import Mathlib.AlgebraicGeometry.Properties

/-!
# ProjectiveLineTopology

The Laurent overlap is dense in both affine charts, hence in the glued projective line.
This proves irreducibility without an extra geometric hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open FLT.Mazur
set_option backward.isDefEq.respectTransparency false
universe u
namespace FLT.Mazur.ProjectiveLineTopology
variable (K : Type u) [Field K]
open ProjectiveLine
theorem overlapLeft_dense : DenseRange (overlapLeft K) :=
  (overlapLeft K).isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace _
theorem overlapRight_dense : DenseRange (overlapRight K) :=
  (overlapRight K).isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace _
theorem torus_dense : DenseRange (overlapLeft K ≫ left K) := by
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro x
  rcases charts_cover K x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · exact by
      have h := image_closure_subset_closure_image (left K).continuous
        (s := Set.range (overlapLeft K)) ⟨y, overlapLeft_dense K y, rfl⟩
      have he : (overlapLeft K ≫ left K : overlap K → scheme K) =
          (left K) ∘ (overlapLeft K) := by ext z; exact Scheme.Hom.comp_apply _ _ _
      rw [he, Set.range_comp]
      exact h
  · rw [overlap_condition]
    exact by
      have h := image_closure_subset_closure_image (right K).continuous
        (s := Set.range (overlapRight K)) ⟨y, overlapRight_dense K y, rfl⟩
      have he : (overlapRight K ≫ right K : overlap K → scheme K) =
          (right K) ∘ (overlapRight K) := by ext z; exact Scheme.Hom.comp_apply _ _ _
      rw [he, Set.range_comp]
      exact h
instance irreducible : IrreducibleSpace (scheme K) := by
  apply (irreducibleSpace_def _).mpr
  change IsIrreducible (Set.univ : Set (scheme K))
  rw [← (torus_dense K).closure_range]
  apply IsIrreducible.closure
  have h := (IrreducibleSpace.isIrreducible_univ (overlap K)).image
    (overlapLeft K ≫ left K) (overlapLeft K ≫ left K).continuous.continuousOn
  simpa only [Set.image_univ] using h
end FLT.Mazur.ProjectiveLineTopology
