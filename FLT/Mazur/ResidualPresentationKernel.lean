/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorKernelFlatCokernel
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Kernel surjectivity after a flat residual presentation

An exact presentation with flat cokernel stays exact at its kernel after
arbitrary tensor coefficients. Applied after a first scalar extension,
this lifts every later presentation relation from the original residual
kernel, without requiring the coefficient algebra to be flat.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.ResidualPresentationKernel
variable {R P N M : Type*} [CommRing R]
  [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
  [AddCommGroup M] [Module R M]

/-- The actual cokernel of an exact presentation inherits flatness from its target. -/
theorem cokernel_flat (f : P →ₗ[R] N) (q : N →ₗ[R] M)
    (he : Function.Exact f q) (hq : Function.Surjective q) [Module.Flat R M] :
    Module.Flat R (N ⧸ f.range) := by
  have hr : f.range = q.ker := (LinearMap.exact_iff.mp he).symm
  rw [hr]
  exact Module.Flat.of_linearEquiv (q.quotKerEquivOfSurjective hq)

/-- Flatness of the actual cokernel makes the canonical tensor-kernel map onto. -/
theorem tensorKer_surjective (f : P →ₗ[R] N) (q : N →ₗ[R] M)
    (he : Function.Exact f q) (hq : Function.Surjective q) [Module.Flat R M]
    (A : Type*) [CommRing A] [Algebra R A] :
    Function.Surjective (LinearMap.tensorKer A A f) := by
  let _ := cokernel_flat f q he hq
  intro x
  obtain ⟨y, hy⟩ := (TensorKernelFlatCokernel.kernel_lTensor_exact f A x.val).mp x.property
  exact ⟨y, Subtype.ext (by simpa only [LinearMap.tensorKer_coe] using hy)⟩

variable (A B : Type*) [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- Every later relation lifts from the kernel after the first scalar extension. -/
theorem exists_kernel_lift (f : P →ₗ[R] N) (q : N →ₗ[R] M)
    (he : Function.Exact f q) (hq : Function.Surjective q)
    [Module.Flat A (A ⊗[R] M)] (z : B ⊗[R] P) (hz : f.baseChange B z = 0) :
    ∃ y : B ⊗[A] (f.baseChange A).ker,
      AlgebraTensorModule.cancelBaseChange R A B B P
        (((f.baseChange A).ker.subtype).baseChange B y) = z := by
  let e := AlgebraTensorModule.cancelBaseChange R A B B P
  have heA : Function.Exact (f.baseChange A) (q.baseChange A) := lTensor_exact A he hq
  have hqA : Function.Surjective (q.baseChange A) := LinearMap.lTensor_surjective A hq
  have hzA : (f.baseChange A).baseChange B (e.symm z) = 0 := by
    rw [LinearMap.baseChange_baseChange]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e, LinearEquiv.apply_symm_apply,
      hz, map_zero]
  obtain ⟨y, hy⟩ := tensorKer_surjective (f.baseChange A) (q.baseChange A)
    heA hqA B ⟨e.symm z, hzA⟩
  refine ⟨y, ?_⟩
  have hv := congrArg Subtype.val hy
  simp only [LinearMap.tensorKer_coe] at hv
  exact (congrArg e hv).trans (e.apply_symm_apply z)

end FLT.Mazur.ResidualPresentationKernel
