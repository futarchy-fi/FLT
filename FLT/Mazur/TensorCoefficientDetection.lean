/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Detecting extended coefficients at original rational points

A nonzero function after an arbitrary field extension has a nonzero original
coefficient. Nonvanishing of that coefficient at an original rational point
forces nonvanishing of the extended function. No algebraicity of the extension
or descent of the extended function is required.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.TensorCoefficientDetection
open scoped TensorProduct
variable {k K A ι : Type*} [Field k] [Field K] [Algebra k K]
  [CommRing A] [Algebra k A]

/-- Evaluate a scalar-extended function at an original rational point. -/
def evaluation (p : A →ₐ[k] k) : K ⊗[k] A →ₐ[k] K :=
  Algebra.TensorProduct.productMap (AlgHom.id k K) ((Algebra.ofId k K).comp p)

/-- Evaluation retains the actual extended scalar. -/
@[simp]
theorem evaluation_tmul (p : A →ₐ[k] k) (x : K) (a : A) :
    evaluation (K := K) p (x ⊗ₜ[k] a) = x * algebraMap k K (p a) := rfl

/-- Taking a scalar coordinate commutes with evaluation at an original point. -/
theorem coordinate_evaluation [DecidableEq ι] (b : Module.Basis ι k K) (p : A →ₐ[k] k)
    (x : K ⊗[k] A) (i : ι) :
    b.repr (evaluation p x) i = p (TensorProduct.equivFinsuppOfBasisLeft b x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul x a =>
    rw [evaluation_tmul, mul_comm, ← Algebra.smul_def,
      map_smul, Finsupp.smul_apply, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    simp [mul_comm]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

/-- A single original coefficient suffices for all original rational points simultaneously. -/
theorem exists_nonzero_detecting_coefficient (x : K ⊗[k] A) (hx : x ≠ 0) :
    ∃ a : A, a ≠ 0 ∧ ∀ p : A →ₐ[k] k,
      p a ≠ 0 → evaluation (K := K) p x ≠ 0 := by
  classical
  let b := Module.Free.chooseBasis k K
  have h : TensorProduct.equivFinsuppOfBasisLeft b x ≠ 0 := by
    intro he
    exact hx ((TensorProduct.equivFinsuppOfBasisLeft b).injective
      (he.trans (map_zero _).symm))
  obtain ⟨i, hi⟩ : ∃ i, TensorProduct.equivFinsuppOfBasisLeft b x i ≠ 0 := by
    by_contra! h'
    exact h (Finsupp.ext h')
  refine ⟨_, hi, fun p hp he ↦ hp ?_⟩
  rw [← coordinate_evaluation b p x i, he, map_zero, Finsupp.zero_apply]

end FLT.Mazur.TensorCoefficientDetection
