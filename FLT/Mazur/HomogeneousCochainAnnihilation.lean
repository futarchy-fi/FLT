/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HomogeneousCochainScaledClass

/-!
# Scalars making a whole cochain homogeneous

A scalar which puts each whole chart value in its full boundary ideal
annihilates the actual correction class, using the scaled cochain itself.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.HomogeneousCochainCorrection
variable {R : Type*} [CommRing R] {ι : Type*}
  {A : ι → Type*} {B : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i j, CommRing (B i j)]
  [∀ i, Algebra R (A i)] [∀ i j, Algebra R (B i j)]
  (p : ∀ i j, A i →ₐ[R] B i j) (q : ∀ i j, A j →ₐ[R] B i j)
  (I : ∀ i, Ideal (A i))

/-- A homogeneous scaled cochain supplies its own exact correction. -/
theorem mem_scalarIdeal_of_smul_mem (v : ∀ i, A i) (s : R)
    (h : ∀ i, s • v i ∈ I i) : s ∈ scalarIdeal p q I v := by
  rw [mem_scalarIdeal_iff_scaled_obstruction, obstruction_eq_zero_iff]
  refine ⟨s • v, h, fun i j ↦ ?_⟩
  simp only [Pi.smul_apply, sub_self, map_zero]

end FLT.Mazur.HomogeneousCochainCorrection
