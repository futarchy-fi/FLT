/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ResidualPresentationKernel

/-!
# The original residual kernel generates every later kernel

The comparison map is constructed using scalar cancellation. Residual
flatness proves that it is onto. Consequently it suffices that the original
kernel maps to zero; the original kernel itself need not be zero.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.ResidualPresentationKernelMap
variable {R P N M : Type*} [CommRing R]
  [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
  [AddCommGroup M] [Module R M]
  (A B : Type*) [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- Extend the old kernel and cancel the intermediate scalar extension. -/
def comparison (f : P →ₗ[R] N) :
    B ⊗[A] (f.baseChange A).ker →ₗ[B] B ⊗[R] P :=
  (AlgebraTensorModule.cancelBaseChange R A B B P).toLinearMap ∘ₗ
    ((f.baseChange A).ker.subtype).baseChange B

/-- The image of each generator is computed in the original presentation. -/
theorem comparison_tmul (f : P →ₗ[R] N) (b : B) (x : (f.baseChange A).ker) :
    comparison A B f (b ⊗ₜ[A] x) =
      AlgebraTensorModule.cancelBaseChange R A B B P (b ⊗ₜ[A] x.val) := rfl

/-- The constructed comparison lands in the later kernel. -/
theorem comparison_mem_kernel (f : P →ₗ[R] N) (y : B ⊗[A] (f.baseChange A).ker) :
    f.baseChange B (comparison A B f y) = 0 := by
  apply (AlgebraTensorModule.cancelBaseChange R A B B N).symm.injective
  rw [map_zero]
  have h := congrArg (fun g ↦ g (((f.baseChange A).ker.subtype).baseChange B y))
    (LinearMap.baseChange_baseChange (B := B) (A := A) f)
  change (f.baseChange A).baseChange B
    (((f.baseChange A).ker.subtype).baseChange B y) =
      (AlgebraTensorModule.cancelBaseChange R A B B N).symm
        (f.baseChange B (comparison A B f y)) at h
  rw [← h]
  have hz : (f.baseChange A).comp (f.baseChange A).ker.subtype = 0 := by
    ext x
    exact x.property
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hz,
    LinearMap.baseChange_zero, LinearMap.zero_apply]

/-- Residual flatness identifies the full later kernel with the comparison image. -/
theorem range_eq_kernel (f : P →ₗ[R] N) (q : N →ₗ[R] M)
    (he : Function.Exact f q) (hq : Function.Surjective q)
    [Module.Flat A (A ⊗[R] M)] :
    (comparison A B f).range = (f.baseChange B).ker := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact comparison_mem_kernel A B f y
  · intro hz
    exact ResidualPresentationKernel.exists_kernel_lift A B f q he hq z hz

/-- It suffices to kill each original kernel element, without assuming that kernel zero. -/
theorem injective_of_kernel_killed (f : P →ₗ[R] N) (q : N →ₗ[R] M)
    (he : Function.Exact f q) (hq : Function.Surjective q)
    [Module.Flat A (A ⊗[R] M)]
    (h : ∀ x : (f.baseChange A).ker, comparison A B f (1 ⊗ₜ[A] x) = 0) :
    Function.Injective (f.baseChange B) := by
  have hc : comparison A B f = 0 := by
    apply LinearMap.ext
    intro y
    change comparison A B f y = 0
    induction y with
    | tmul b x =>
      have hb : b ⊗ₜ[A] x = b • (1 ⊗ₜ[A] x) := by
        rw [smul_tmul', smul_eq_mul, mul_one]
      rw [hb, map_smul, h, smul_zero]
    | add x y hx hy => rw [map_add, hx, hy, add_zero]
  apply LinearMap.ker_eq_bot.mp
  rw [← range_eq_kernel A B f q he hq, hc, LinearMap.range_zero]

end FLT.Mazur.ResidualPresentationKernelMap
