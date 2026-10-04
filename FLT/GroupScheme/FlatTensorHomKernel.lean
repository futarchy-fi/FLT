/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RingTheory.Flat.Equalizer

/-! # Flat tensoring of relations on finite projective coordinate modules -/

@[expose] public noncomputable section
open TensorProduct
namespace LinearMap
variable {R U V M T : Type*} [CommRing R]
  [AddCommGroup U] [AddCommGroup V] [AddCommGroup M] [AddCommGroup T]
  [Module R U] [Module R V] [Module R M] [Module R T]

/-- Impose relations by precomposing a functional with the relation map. -/
def relationPrecomp (r : U →ₗ[R] V) : (V →ₗ[R] M) →ₗ[R] (U →ₗ[R] M) where
  toFun f := f.comp r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [Module.Projective R U] [Module.Finite R U]
  [Module.Projective R V] [Module.Finite R V]

/-- The canonical Hom/tensor comparisons commute with the original relations. -/
theorem relationPrecomp_tensor (r : U →ₗ[R] V) (z : T ⊗[R] (V →ₗ[R] M)) :
    lTensorHomEquivHomLTensor R U T M ((relationPrecomp r).lTensor T z) =
      relationPrecomp r (lTensorHomEquivHomLTensor R V T M z) := by
  induction z using TensorProduct.inductionOn with
  | tmul t f =>
    ext u
    simp [relationPrecomp]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Restrict the coordinate Hom/tensor equivalence to the exact relation kernel. -/
def relationKernelTensorEquiv (r : U →ₗ[R] V) :
    ker ((relationPrecomp (M := M) r).lTensor T) ≃ₗ[R]
      ker (relationPrecomp (M := T ⊗[R] M) r) where
  toFun z := ⟨lTensorHomEquivHomLTensor R V T M z, by
    rw [mem_ker, ← relationPrecomp_tensor, show
      (relationPrecomp (M := M) r).lTensor T z.val = 0 from z.property, map_zero]⟩
  invFun z := ⟨(lTensorHomEquivHomLTensor R V T M).symm z, by
    apply (lTensorHomEquivHomLTensor R U T M).injective
    rw [relationPrecomp_tensor, LinearEquiv.apply_symm_apply, map_zero]
    exact z.property⟩
  left_inv z := by apply Subtype.ext; exact LinearEquiv.symm_apply_apply _ _
  right_inv z := by apply Subtype.ext; exact LinearEquiv.apply_symm_apply _ _
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  map_smul' a x := by apply Subtype.ext; exact map_smul _ _ _

/-- Flat tensoring commutes with the relation kernel; the quotient need not be projective. -/
def flatTensorHomKernelEquiv [Module.Flat R T] (r : U →ₗ[R] V) :
    T ⊗[R] ker (relationPrecomp (M := M) r) ≃ₗ[R]
      ker (relationPrecomp (M := T ⊗[R] M) r) :=
  (tensorKerEquiv R T (relationPrecomp r)).trans (relationKernelTensorEquiv r)

/-- Evaluation retains the original coordinate functional and tensor factor. -/
theorem flatTensorHomKernelEquiv_tmul [Module.Flat R T] (r : U →ₗ[R] V)
    (t : T) (f : ker (relationPrecomp (M := M) r)) (v : V) :
    (flatTensorHomKernelEquiv r (t ⊗ₜ[R] f)).val v = t ⊗ₜ[R] f.val v := by
  change lTensorHomEquivHomLTensor R V T M (t ⊗ₜ[R] f.val) v = _
  simp

end LinearMap
