/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupEnvelopeNeighborhood
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Stable affine neighborhoods in a closed subscheme of an affine open

A closed immersion into an open affine envelope supplies a common affine
neighborhood of each finite orbit. Taking the invariant core yields an actual
stable affine source open; the action need not extend to the envelope.
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

/-- Every finite stable subset has an affine invariant neighborhood in the original source. -/
theorem exists_closed_envelope_stable_affine (s : Set X) (hs : s.Finite)
    (hi : ∀ g : G, (ρ g).hom '' s ⊆ s) :
    ∃ U : X.Opens, IsAffineOpen U ∧ s ⊆ U ∧
      ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U := by
  let _ : X.IsSeparated := ⟨by
    rw [← terminal.comp_from (j ≫ k)]
    infer_instance⟩
  obtain ⟨V, hV, hsV, _⟩ := AffineEnvelopeFiniteNeighborhood.exists_affineOpen
    k ⊤ (j '' s) (hs.image _) (by intro x hx; trivial)
  let W := j ⁻¹ᵁ V
  have hW : IsAffineOpen W := hV.preimage j
  refine ⟨invariantCore ρ W, isAffineOpen_invariantCore ρ W hW, ?_,
    invariantCore_preimage ρ W⟩
  intro x hx
  apply (mem_invariantCore ρ W x).mpr
  intro g
  exact hsV (Set.mem_image_of_mem j (hi g ⟨x, hx, rfl⟩))

/-- Every point lies in a stable affine open, for an action that may move all endpoint maps. -/
theorem exists_closed_envelope_orbit_affine (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U := by
  let s := Set.range fun g : G ↦ (ρ g).hom x
  have hi (g : G) : (ρ g).hom '' s ⊆ s := by
    rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
    exact ⟨g * h, (action_mul_apply ρ g h x).symm⟩
  obtain ⟨U, hU, hsU, he⟩ :=
    exists_closed_envelope_stable_affine ρ j k s (Set.finite_range _) hi
  refine ⟨U, hU, hsU ?_, he⟩
  refine ⟨1, ?_⟩
  change (ρ 1).hom x = x
  rw [map_one]
  rfl

end FLT.Mazur.FiniteGroupNeighborhood
