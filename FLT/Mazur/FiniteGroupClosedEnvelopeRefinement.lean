/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupClosedEnvelopeNeighborhood

/-!
# Refining moving affine charts inside prescribed source opens

A finite stable set in a closed subscheme of an open affine envelope has a
stable affine neighborhood inside any prescribed open containing the set.
In particular, charts have common refinements on their actual source overlaps.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteGroupNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type} [Group G] [Finite G] {X Y Z : Scheme}
  (ρ : G →* Aut X) (j : X ⟶ Y) [IsClosedImmersion j]
  (k : Y ⟶ Z) [IsOpenImmersion k] [IsAffine Z]

include j k

/-- Closed envelopes supply stable affine refinements inside a prescribed source open. -/
theorem exists_closed_envelope_affine_refinement (s : Set X) (hs : s.Finite)
    (hi : ∀ g : G, (ρ g).hom '' s ⊆ s) (W : X.Opens) (hsW : s ⊆ W) :
    ∃ U : X.Opens, IsAffineOpen U ∧ s ⊆ U ∧ U ≤ W ∧
      ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U := by
  let _ : X.IsSeparated := ⟨by
    rw [← terminal.comp_from (j ≫ k)]
    infer_instance⟩
  let V : Y.Opens := ⟨(j '' (W : Set X)ᶜ)ᶜ,
    (j.isClosedEmbedding.isClosedMap _ W.isOpen.isClosed_compl).isOpen_compl⟩
  have hsV : j '' s ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
    exact hy (j.isClosedEmbedding.injective he ▸ hsW hx)
  obtain ⟨B, hB, hsB, hBV⟩ :=
    AffineEnvelopeFiniteNeighborhood.exists_affineOpen k V (j '' s) (hs.image _) hsV
  let T := j ⁻¹ᵁ B
  have hT : IsAffineOpen T := hB.preimage j
  refine ⟨invariantCore ρ T, isAffineOpen_invariantCore ρ T hT, ?_, ?_,
    invariantCore_preimage ρ T⟩
  · intro x hx
    exact (mem_invariantCore ρ T x).mpr fun g ↦
      hsB (Set.mem_image_of_mem j (hi g ⟨x, hx, rfl⟩))
  · intro x hx
    have hv := hBV (invariantCore_le ρ T hx)
    by_contra hn
    exact hv ⟨x, hn, rfl⟩

/-- A point in a stable open has a stable affine neighborhood contained in that open. -/
theorem exists_closed_envelope_affine_basis (W : X.Opens)
    (hW : ∀ g : G, (ρ g).hom ⁻¹ᵁ W = W) (x : X) (hx : x ∈ W) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ W ∧
      ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U := by
  let s := Set.range fun g : G ↦ (ρ g).hom x
  have hi (g : G) : (ρ g).hom '' s ⊆ s := by
    rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
    exact ⟨g * h, (action_mul_apply ρ g h x).symm⟩
  have hsW : s ⊆ W := by
    rintro _ ⟨g, rfl⟩
    change x ∈ (ρ g).hom ⁻¹ᵁ W
    rwa [hW]
  obtain ⟨U, hU, hsU, hUW, he⟩ :=
    exists_closed_envelope_affine_refinement ρ j k s (Set.finite_range _) hi W hsW
  refine ⟨U, hU, hsU ?_, hUW, he⟩
  refine ⟨1, ?_⟩
  change (ρ 1).hom x = x
  rw [map_one]
  rfl

end FLT.Mazur.FiniteGroupNeighborhood
