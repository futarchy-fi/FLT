/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Affine neighborhoods in the original input from closed-fiber maps

A map on a closed subscheme determines actual affine neighborhoods in the
original source whose closed-fiber images lie in a fixed affine target.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ClosedFiberAffineNeighborhood
universe u
variable {Z X Y : Scheme.{u}} (j : Z ⟶ X) [IsClosedImmersion j] (f : Z ⟶ Y)

/-- A target open pulls back to the restriction of an actual original-source open. -/
theorem exists_open (V : Y.Opens) : ∃ W : X.Opens, j ⁻¹ᵁ W = f ⁻¹ᵁ V := by
  obtain ⟨W, hW, he⟩ := j.isClosedEmbedding.isInducing.isOpen_iff.mp (f ⁻¹ᵁ V).isOpen
  exact ⟨⟨W, hW⟩, TopologicalSpace.Opens.ext he⟩

/-- Refine at an original point, retaining the chosen target open. -/
theorem exists_affine (V : Y.Opens) (z : Z) (hz : f z ∈ V) :
    ∃ U : X.affineOpens, j z ∈ U.1 ∧ j ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ V := by
  obtain ⟨W, hW⟩ := exists_open j f V
  have hzW : j z ∈ W := by
    change z ∈ j ⁻¹ᵁ W
    rw [hW]
    exact hz
  obtain ⟨U, hU, hzU, hUW⟩ := exists_isAffineOpen_mem_and_subset hzW
  refine ⟨⟨U, hU⟩, hzU, ?_⟩
  rw [← hW]
  exact fun _ hx ↦ hUW hx

/-- Every point of the original closed fiber has an affine source/target pair. -/
theorem exists_affine_pair (z : Z) :
    ∃ (U : X.affineOpens) (V : Y.affineOpens),
      j z ∈ U.1 ∧ f z ∈ V.1 ∧ j ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ V.1 := by
  obtain ⟨V, hV, hzV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f z ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨U, hzU, hUV⟩ := exists_affine j f V z hzV
  exact ⟨U, ⟨V, hV⟩, hzU, hzV, hUV⟩

end FLT.Mazur.ClosedFiberAffineNeighborhood
