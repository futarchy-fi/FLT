/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEnvelopeFiniteNeighborhood
public import FLT.Mazur.FiniteGroupAffineNeighborhood
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Stable affine neighborhoods from an affine envelope

An open affine envelope supplies a common neighborhood of a finite stable
set. The existing invariant-core construction makes it group-stable.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteGroupNeighborhood
set_option backward.isDefEq.respectTransparency false
variable {G : Type} [Group G] [Finite G] {X : Scheme} (ρ : G →* Aut X)

/-- A finite stable set in an affine envelope has an actual stable affine neighborhood. -/
theorem exists_stable_affine_neighborhood {Y : Scheme} [IsAffine Y]
    (j : X ⟶ Y) [IsOpenImmersion j] (s : Set X) (hs : s.Finite)
    (hi : ∀ g : G, (ρ g).hom '' s ⊆ s) (W : X.Opens) (hsW : s ⊆ W) :
    ∃ U : X.Opens, IsAffineOpen U ∧ s ⊆ U ∧ U ≤ W ∧
      ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U := by
  let _ : X.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from j]
    infer_instance⟩
  obtain ⟨B, hB, hsB, hBW⟩ :=
    AffineEnvelopeFiniteNeighborhood.exists_affineOpen j W s hs hsW
  exact ⟨invariantCore ρ B, isAffineOpen_invariantCore ρ B hB,
    (fun x hx ↦ (mem_invariantCore ρ B x).mpr
      fun g ↦ hsB (hi g ⟨x, hx, rfl⟩)),
    (invariantCore_le ρ B).trans hBW, invariantCore_preimage ρ B⟩

end FLT.Mazur.FiniteGroupNeighborhood
