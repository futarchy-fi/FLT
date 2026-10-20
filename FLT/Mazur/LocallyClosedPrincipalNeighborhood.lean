/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEnvelopeFiniteNeighborhood
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Affine principal neighborhoods in a locally closed affine envelope

A finite set in a closed subscheme of an affine open has a common affine
principal neighborhood inside any prescribed open. The parameter is an actual
global section pulled from the original affine envelope.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.LocallyClosedPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
variable {X Y Z : Scheme} (j : X ⟶ Y) [IsClosedImmersion j]
  (k : Y ⟶ Z) [IsOpenImmersion k] [IsAffine Z]

include j k in
/-- Finite subsets have affine principal refinements with unchanged scheme structure. -/
theorem exists_affine_principal (W : X.Opens) (s : Set X) (hs : s.Finite) (hsW : s ⊆ W) :
    ∃ a : Γ(X, ⊤), IsAffineOpen (X.basicOpen a) ∧ s ⊆ X.basicOpen a ∧ X.basicOpen a ≤ W := by
  obtain ⟨T, hT, he⟩ := (j.isClosedEmbedding.isEmbedding.isInducing.isOpen_iff).mp W.isOpen
  let V : Y.Opens := ⟨T, hT⟩
  have hV : j ⁻¹ᵁ V = W := TopologicalSpace.Opens.ext he
  obtain ⟨a, ha, haV⟩ := AffineEnvelopeFiniteNeighborhood.exists_envelope_principal
    (k ''ᵁ V) ((j ≫ k) '' s) (hs.image _) (by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨j x, ?_, rfl⟩
      change x ∈ j ⁻¹ᵁ V
      rw [hV]
      exact hsW hx)
  have hka : IsAffineOpen (k ⁻¹ᵁ Z.basicOpen a) :=
    ((isAffineOpen_top Z).basicOpen a).preimage_of_isOpenImmersion k
      (haV.trans (by rintro _ ⟨y, _, rfl⟩; exact ⟨y, rfl⟩))
  refine ⟨(j ≫ k).appTop a, ?_, ?_, ?_⟩
  · rw [← Scheme.preimage_basicOpen_top, Scheme.Hom.comp_preimage]
    exact hka.preimage j
  · rw [← Scheme.preimage_basicOpen_top]
    exact fun x hx ↦ ha (Set.mem_image_of_mem _ hx)
  · rw [← Scheme.preimage_basicOpen_top, Scheme.Hom.comp_preimage, ← hV]
    apply j.preimage_mono
    rw [← k.preimage_image_eq V]
    exact k.preimage_mono haV

end FLT.Mazur.LocallyClosedPrincipalNeighborhood
