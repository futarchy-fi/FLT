/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ImmersionAffineLifts

/-!
# Ambient neighborhoods of an open inside a closed subscheme

Remove the image of the closed complement. The resulting ambient open has
exactly the prescribed inverse image, so restricting to it loses no part of
the closed subscheme outside the chosen open immersion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ClosedImmersionOpenNeighborhood
variable {X Y Z : Scheme} (j : X ⟶ Y) (f : Y ⟶ Z)
  [IsOpenImmersion j] [IsClosedImmersion f]

/-- The complement of the closed image of the unwanted part of the middle scheme. -/
def neighborhood : Z.Opens :=
  ⟨(f '' (j.opensRange : Set Y)ᶜ)ᶜ,
    (f.isClosedEmbedding.isClosedMap _ j.opensRange.isOpen.isClosed_compl).isOpen_compl⟩

/-- The full closed inverse image is exactly the original open immersion's range. -/
theorem preimage_neighborhood : f ⁻¹ᵁ neighborhood j f = j.opensRange := by
  ext y
  change f y ∉ f '' (j.opensRange : Set Y)ᶜ ↔ y ∈ j.opensRange
  rw [f.isClosedEmbedding.injective.mem_set_image]
  exact not_not

/-- Every point of the original open lies in the constructed ambient neighborhood. -/
theorem mem_neighborhood (x : X) : (j ≫ f) x ∈ neighborhood j f := by
  change j x ∈ f ⁻¹ᵁ neighborhood j f
  rw [preimage_neighborhood]
  exact ⟨x, rfl⟩

/-- Affine coborder patches can be refined so their full closed inverse image lies in the open. -/
theorem exists_refined_patch (x : X) (U : (j ≫ f).coborderRange.toScheme.Opens)
    (hx : (j ≫ f).liftCoborder x ∈ U) :
    ∃ V : (j ≫ f).coborderRange.toScheme.affineOpens,
      x ∈ (ImmersionAffineLifts.source (j ≫ f) V).1 ∧ V.1 ≤ U ∧
      (ImmersionAffineLifts.target (j ≫ f) V).1 ≤ neighborhood j f := by
  let N := (j ≫ f).coborderRange.ι ⁻¹ᵁ neighborhood j f
  have hn : (j ≫ f).liftCoborder x ∈ N := by
    change ((j ≫ f).liftCoborder ≫ (j ≫ f).coborderRange.ι) x ∈ neighborhood j f
    rw [Scheme.Hom.liftCoborder_ι]
    exact mem_neighborhood j f x
  obtain ⟨_, ⟨V, hV, rfl⟩, hv, hle⟩ :=
    (j ≫ f).coborderRange.toScheme.isBasis_affineOpens.exists_subset_of_mem_open
      (show (j ≫ f).liftCoborder x ∈ U ⊓ N from ⟨hx, hn⟩) (U ⊓ N).isOpen
  refine ⟨⟨V, hV⟩, hv, fun y hy => (hle hy).1, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact (hle hy).2

/-- On every refined patch, all closed-subscheme points belong to the original open. -/
theorem preimage_le_range (W : Z.Opens) (hW : W ≤ neighborhood j f) :
    f ⁻¹ᵁ W ≤ j.opensRange := by
  rw [← preimage_neighborhood j f]
  exact fun _ hy => hW hy

end FLT.Mazur.ClosedImmersionOpenNeighborhood
