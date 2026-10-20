/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionBoundaryKernel

/-!
# Original boundary lifts kill the extended obstruction map

If every original boundary section has compatible lifts, the obstruction map
vanishes after every scalar extension. Flatness is unnecessary in this direction.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.BoundaryCorrectionIdeal
variable {R : Type*} [CommRing R] {ι : Type*} {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)] [∀ i j, Algebra R (C i j)]
  (φ : ∀ i, A i →ₐ[R] B i)
  (p : ∀ i j, A i →ₐ[R] C i j) (q : ∀ i j, A j →ₐ[R] C i j)
  (v : ∀ i, A i) {D : Type*} [AddCommGroup D] [Module R D]
  (β : D →ₗ[R] (∀ i, B i)) (S : Type*) [CommRing S] [Algebra R S]

/-- Exact original lifts kill every extended boundary class, even for nonflat scalars. -/
theorem boundaryCokernelMap_eq_zero_of_original
    (h : originalBoundaryCokernelMap φ p q v β = 0) :
    boundaryCokernelMap φ p q v β S = 0 := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul s t =>
    exact boundaryCokernelMap_tmul_eq_zero φ p q v β S t
      (by rw [h]; rfl) s
  | add x y hx hy => simp only [map_add, hx, hy]

end FLT.Mazur.BoundaryCorrectionIdeal
