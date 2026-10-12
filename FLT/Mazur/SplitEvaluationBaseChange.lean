/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SplitEvaluationTensorKernel
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Arbitrary base change of split exact evaluation

A chosen section gives a retraction onto the kernel. Extending these identities
proves that the tensor of the kernel embeds and equals the new kernel, even for
nonflat coefficient extensions.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.Approximation
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
  (ε : M →ₗ[R] N) (σ : N →ₗ[R] M) (h : ε.comp σ = LinearMap.id)
  (T : Type*) [CommRing T] [Algebra R T]

include h in
/-- The kernel inclusion stays injective under every coefficient extension. -/
theorem splitEvaluation_baseChange_subtype_injective :
    Function.Injective (ε.ker.subtype.baseChange T) := by
  have he := congrArg (LinearMap.baseChange T)
    (splitEvaluationKernelProjection_subtype ε σ h)
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at he
  exact Function.HasLeftInverse.injective
    ⟨(splitEvaluationKernelProjection ε σ h).baseChange T, LinearMap.congr_fun he⟩

include h in
/-- The scalar extension of the kernel is exactly the extended evaluation kernel. -/
theorem splitEvaluation_baseChange_kernel :
    ε.ker.baseChange T = LinearMap.ker (ε.baseChange T) := by
  let π := splitEvaluationKernelProjection ε σ h
  have hz : (ε.baseChange T).comp (ε.ker.subtype.baseChange T) = 0 := by
    have he : ε.comp ε.ker.subtype = 0 := by ext x; exact x.property
    rw [← LinearMap.baseChange_comp, he, LinearMap.baseChange_zero]
  have hd : (ε.ker.subtype.baseChange T).comp (π.baseChange T) =
      LinearMap.id - (σ.baseChange T).comp (ε.baseChange T) := by
    rw [← LinearMap.baseChange_comp, subtype_splitEvaluationKernelProjection,
      LinearMap.baseChange_sub, LinearMap.baseChange_id, LinearMap.baseChange_comp]
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact LinearMap.congr_fun hz x
  · intro x hx
    refine ⟨π.baseChange T x, ?_⟩
    have he := LinearMap.congr_fun hd x
    simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.mem_ker.mp hx, map_zero, sub_zero] using he

/-- Tensoring the split kernel is linearly equivalent to the entire new kernel. -/
def splitEvaluationBaseChangeKernelEquiv :
    T ⊗[R] ε.ker ≃ₗ[T] LinearMap.ker (ε.baseChange T) :=
  (LinearEquiv.ofInjective (ε.ker.subtype.baseChange T)
    (splitEvaluation_baseChange_subtype_injective ε σ h T)).trans
      (LinearEquiv.ofEq _ _ (splitEvaluation_baseChange_kernel ε σ h T))

end FLT.Mazur.Approximation
