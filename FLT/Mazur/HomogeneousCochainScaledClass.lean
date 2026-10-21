/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HomogeneousCochainScalarObstruction

/-!
# Scalar membership as vanishing of a scaled cochain class

This criterion keeps the quotient's scalar instances inside the general
cochain API, so geometric specializations need only one direct application.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.HomogeneousCochainCorrection
variable {R : Type*} [CommRing R] {ι : Type*}
  {A : ι → Type*} {B : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i j, CommRing (B i j)]
  [∀ i, Algebra R (A i)] [∀ i j, Algebra R (B i j)]
  (p : ∀ i j, A i →ₐ[R] B i j) (q : ∀ i j, A j →ₐ[R] B i j)
  (I : ∀ i, Ideal (A i))

/-- A scalar is admissible exactly when the scaled cochain has zero correction class. -/
theorem mem_scalarIdeal_iff_scaled_obstruction (v : ∀ i, A i) (s : R) :
    s ∈ scalarIdeal p q I v ↔ obstruction p q I (s • v) = 0 := by
  rw [obstruction_smul, mem_scalarIdeal]

end FLT.Mazur.HomogeneousCochainCorrection
