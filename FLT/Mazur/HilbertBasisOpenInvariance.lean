/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBasisOpen

/-!
# Independence of the reference basis in the basis open

The determinant open depends only on the proposed vectors. Linear equivalences
preserve it, so different trivializations of a family give the same open.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.HilbertChart

variable {S A B : Type*} [CommRing S] [CommRing A] [CommRing B]
variable [Algebra S A] [Algebra S B] {d : ℕ}

/-- Changing the reference basis does not change the actual open subset of the spectrum. -/
theorem basisOpen_independent (b c : Module.Basis (Fin d) S A) (y : Fin d → A) :
    basisOpen b y = basisOpen c y := by
  ext p
  change p ∈ basisOpen b y ↔ p ∈ basisOpen c y
  rw [mem_basisOpen_iff, mem_basisOpen_iff]

/-- Transporting both the reference basis and the proposed vectors preserves the determinant. -/
theorem basisDeterminant_map (b : Module.Basis (Fin d) S A) (y : Fin d → A)
    (e : A ≃ₗ[S] B) :
    basisDeterminant (b.map e) (e ∘ y) = basisDeterminant b y := by
  rw [basisDeterminant, Module.Basis.det_map]
  congr 1
  ext i
  exact e.symm_apply_apply (y i)

/-- An arbitrary trivialization of an isomorphic family computes the same basis open. -/
theorem basisOpen_equiv (b : Module.Basis (Fin d) S A) (c : Module.Basis (Fin d) S B)
    (y : Fin d → A) (e : A ≃ₗ[S] B) :
    basisOpen c (e ∘ y) = basisOpen b y := by
  rw [basisOpen_independent c (b.map e), basisOpen, basisDeterminant_map]
  rfl

end FLT.Mazur.HilbertChart
