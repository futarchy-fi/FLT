/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEnvelopeFiniteNeighborhood

/-!
# Refining an affine neighborhood around an entire finite set

Once a finite set is contained in one affine open, it admits a smaller affine
neighborhood inside any prescribed ambient open containing the whole set.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineEnvelopeFiniteNeighborhood
universe u
variable {X : Scheme.{u}}

/-- Refine a known affine neighborhood inside an arbitrary prescribed open around the whole set. -/
theorem refine_affineOpen (A : X.Opens) (hA : IsAffineOpen A) (W : X.Opens)
    (t : Set X) (ht : t.Finite) (htA : t ⊆ A) (htW : t ⊆ W) :
    ∃ B : X.Opens, IsAffineOpen B ∧ t ⊆ B ∧ B ≤ A ⊓ W := by
  let _ : IsAffine A.toScheme := hA
  let s : Set A.toScheme := {x | x.val ∈ t}
  have hs : s.Finite := ht.preimage Subtype.val_injective.injOn
  obtain ⟨B, hB, hsB, hBW⟩ := exists_affineOpen (𝟙 A.toScheme) (A.ι ⁻¹ᵁ W) s hs
    (fun x hx ↦ htW hx)
  refine ⟨A.ι ''ᵁ B, hB.image_of_isOpenImmersion A.ι, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, htA hx⟩, hsB hx, rfl⟩
  · rintro x ⟨y, hy, rfl⟩
    exact ⟨y.property, hBW hy⟩

end FLT.Mazur.AffineEnvelopeFiniteNeighborhood
