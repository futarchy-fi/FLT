/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AlgebraicTensorCoefficientOrbit

/-!
# Conjugating rational points while retaining original coordinates

Coefficient conjugacy acts on the values of the original affine coordinates.
The resulting point remains linear over the algebraic coefficient field.
Its evaluation is compared with the inverse coefficient action on functions.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.AlgebraicTensorCoefficientOrbit
open scoped TensorProduct
variable {k L A : Type*} [Field k] [Field L] [Algebra k L]
  [CommRing A] [Algebra k A]

/-- Evaluate original coordinates after applying a coefficient automorphism to their values. -/
def conjugatePoint (p : L ⊗[k] A →ₐ[L] L) (σ : L ≃ₐ[k] L) : L ⊗[k] A →ₐ[L] L :=
  Algebra.TensorProduct.lift (AlgHom.id L L)
    (σ.toAlgHom.comp ((p.restrictScalars k).comp Algebra.TensorProduct.includeRight))
    (fun _ _ ↦ Commute.all _ _)

/-- An original-coordinate formula for the conjugate point. -/
@[simp]
theorem conjugatePoint_tmul (p : L ⊗[k] A →ₐ[L] L) (σ : L ≃ₐ[k] L) (l : L) (a : A) :
    conjugatePoint p σ (l ⊗ₜ[k] a) = l * σ (p (1 ⊗ₜ[k] a)) := rfl

/-- Evaluation of a pure tensor separates the scalar and original coordinate. -/
theorem point_tmul (p : L ⊗[k] A →ₐ[L] L) (l : L) (a : A) :
    p (l ⊗ₜ[k] a) = l * p (1 ⊗ₜ[k] a) := by
  have h : l ⊗ₜ[k] a = l • (1 ⊗ₜ[k] a) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h, map_smul, smul_eq_mul]

/-- Conjugacy transports the whole evaluation, not just the underlying spectrum point. -/
theorem conjugatePoint_action (p : L ⊗[k] A →ₐ[L] L) (σ : L ≃ₐ[k] L) (x : L ⊗[k] A) :
    conjugatePoint p σ (action σ x) = σ (p x) := by
  induction x using TensorProduct.inductionOn with
  | tmul l a => rw [action_tmul, conjugatePoint_tmul, point_tmul p l a, map_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Nonvanishing at the conjugate point is tested on the inverse conjugate function. -/
theorem conjugatePoint_ne_zero_iff (p : L ⊗[k] A →ₐ[L] L)
    (σ : L ≃ₐ[k] L) (x : L ⊗[k] A) :
    conjugatePoint p σ x ≠ 0 ↔ p ((action σ).symm x) ≠ 0 := by
  have h := conjugatePoint_action p σ ((action σ).symm x)
  rw [AlgEquiv.apply_symm_apply] at h
  rw [h, ne_eq, map_eq_zero_iff σ σ.injective]

end FLT.Mazur.AlgebraicTensorCoefficientOrbit
