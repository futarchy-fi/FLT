/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationMixedFrameRelation
public import FLT.Mazur.EquivalenceRelationCompleteInterior

/-!
# Complete neighborhoods transfer between independently distinguished frames

An original arrow transports the complete interior to any other frame of the
same size, including a different distinguished label. Both projections use
the entire original relation. This does not infer an arrow from scalar equality.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
open RelativeOrderedTuples EquivalenceRelationOrderedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o o' : I)

include e

local instance mixedInteriorOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance mixedInteriorOver_etale : Etale (Over.mk p).hom := ‹Etale p›

/-- A complete frame forces completeness of any equally sized original related frame. -/
theorem complete_of_mixed_original_arrow {K : Type} [Field K]
    (u : Spec (.of K) ⟶ source p q I o) (v : Spec (.of K) ⟶ source p q I o')
    (a : Spec (.of K) ⟶ D) (ha : a ≫ p = u ≫ first p q I o)
    (hb : a ≫ q = v ≫ first p q I o') (hu : Complete I o u) : Complete I o' v := by
  have ht := comparisonFrame_complete e I o u hu a ha
  have hv := complete_of_complete_frame (Over.mk p) I (comparisonFrame e I o u a ha)
    (targetFrame I o' v a hb) ht
  have hc := frameCast_complete I hb (targetFrame I o' v a hb) hv
  have he : frameCast I hb (targetFrame I o' v a hb) = testFrame I o' v := by
    apply Over.OverMorphism.ext
    rfl
  rwa [he] at hc

/-- Intrinsic completeness agrees at both independently labeled original endpoints. -/
theorem completePointLocus_mixed_invariant :
    fst p q I I o o' ⁻¹' completePointLocus (p := p) (q := q) I o =
      snd p q I I o o' ⁻¹' completePointLocus (p := p) (q := q) I o' := by
  ext x
  let z := (relation p q I I o o').fromSpecResidueField x
  have hx : z default = x := Scheme.fromSpecResidueField_apply x default
  have h₁ : (z ≫ arrow p q I I o o') ≫ p =
      (z ≫ fst p q I I o o') ≫ first p q I o := by
    simp only [Category.assoc, arrow_first]
  have h₂ : (z ≫ arrow p q I I o o') ≫ q =
      (z ≫ snd p q I I o o') ≫ first p q I o' := by
    simp only [Category.assoc, arrow_second]
  have H : Complete I o (z ≫ fst p q I I o o') ↔
      Complete I o' (z ≫ snd p q I I o o') := by
    refine ⟨complete_of_mixed_original_arrow e I o o' _ _ _ h₁ h₂, ?_⟩
    exact complete_of_mixed_original_arrow e I o' o _ _
      ((z ≫ arrow p q I I o o') ≫ e.s)
      (by rw [Category.assoc, e.symmetry₁]; exact h₂)
      (by rw [Category.assoc, e.symmetry₂]; exact h₁)
  rw [complete_iff_mem_completePointLocus, complete_iff_mem_completePointLocus] at H
  change fst p q I I o o' (z default) ∈ _ ↔ snd p q I I o o' (z default) ∈ _ at H
  rwa [hx] at H

/-- The first mixed projection is etale even with independent finite label types. -/
theorem mixed_fst_etale (J : Type) [Fintype J] (j : J) : Etale (fst p q I J o j) := by
  let _ := first_etale e J j
  change Etale (pullback.fst (leftRelationTarget p q I o) (first p q J j) ≫
    pullback.fst (first p q I o) p)
  infer_instance

variable [Etale q]

/-- The second mixed projection is etale on the whole original relation. -/
theorem mixed_snd_etale (J : Type) [Fintype J] (j : J) : Etale (snd p q I J o j) := by
  let _ := first_etale e I o
  let _ : Etale (leftRelationTarget p q I o) :=
    inferInstanceAs (Etale (pullback.snd (first p q I o) p ≫ q))
  exact inferInstanceAs (Etale (pullback.snd (leftRelationTarget p q I o) (first p q J j)))

/-- Complete neighborhoods, and not just complete points, transfer along every mixed arrow. -/
theorem completeInterior_mixed_invariant :
    fst p q I I o o' ⁻¹ᵁ completeInterior (p := p) (q := q) I o =
      snd p q I I o o' ⁻¹ᵁ completeInterior (p := p) (q := q) I o' := by
  let _ := mixed_fst_etale e I o I o'
  let _ := mixed_snd_etale e I o I o'
  apply TopologicalSpace.Opens.ext
  change (fst p q I I o o') ⁻¹' interior _ = (snd p q I I o o') ⁻¹' interior _
  rw [(fst p q I I o o').isOpenMap.preimage_interior_eq_interior_preimage
    (fst p q I I o o').continuous,
    (snd p q I I o o').isOpenMap.preimage_interior_eq_interior_preimage
    (snd p q I I o o').continuous, completePointLocus_mixed_invariant e I o o']

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
