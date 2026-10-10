/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Scalar extension of a split evaluation kernel

A linear evaluation with a specified section has a split kernel inclusion.
Tensoring this splitting works for every module, without flatness. Thus
injectivity after scalar extension is exactly vanishing of the extended
kernel. A finite source also makes the kernel finite.
-/

@[expose] public noncomputable section

open TensorProduct

namespace FLT.Mazur.Approximation

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
  (ε : M →ₗ[R] N) (σ : N →ₗ[R] M) (h : ε.comp σ = LinearMap.id)

/-- Subtraction of the evaluated scalar projects onto the evaluation kernel. -/
def splitEvaluationKernelProjection : M →ₗ[R] ε.ker :=
  (LinearMap.id - σ.comp ε).codRestrict ε.ker fun m ↦ by
    change ε (m - σ (ε m)) = 0
    rw [map_sub, ← LinearMap.comp_apply, h, LinearMap.id_apply, sub_self]

/-- The kernel projection retracts the original kernel inclusion. -/
theorem splitEvaluationKernelProjection_subtype :
    (splitEvaluationKernelProjection ε σ h).comp ε.ker.subtype = LinearMap.id := by
  ext x
  simp [splitEvaluationKernelProjection]

/-- The complementary projector is subtraction of the split evaluation. -/
theorem subtype_splitEvaluationKernelProjection :
    ε.ker.subtype.comp (splitEvaluationKernelProjection ε σ h) =
      LinearMap.id - σ.comp ε := rfl

include h in
/-- The evaluation kernel of a finite module is finite, without a Noetherian hypothesis. -/
theorem finite_splitEvaluationKernel [Module.Finite R M] : Module.Finite R ε.ker := by
  apply Module.Finite.of_surjective (splitEvaluationKernelProjection ε σ h)
  exact Function.HasRightInverse.surjective
    ⟨ε.ker.subtype, LinearMap.congr_fun (splitEvaluationKernelProjection_subtype ε σ h)⟩

include h in
/-- Tensoring a split evaluation is injective precisely when its extended kernel vanishes. -/
theorem splitEvaluation_lTensor_injective_iff (T : Type*) [AddCommGroup T] [Module R T] :
    Function.Injective (ε.lTensor T) ↔ Subsingleton (T ⊗[R] ε.ker) := by
  let π := splitEvaluationKernelProjection ε σ h
  have hi : Function.Injective (ε.ker.subtype.lTensor T) := by
    have he := congrArg (LinearMap.lTensor T)
      (splitEvaluationKernelProjection_subtype ε σ h)
    rw [LinearMap.lTensor_comp, LinearMap.lTensor_id] at he
    exact Function.HasLeftInverse.injective ⟨π.lTensor T, LinearMap.congr_fun he⟩
  have hz : (ε.lTensor T).comp (ε.ker.subtype.lTensor T) = 0 := by
    have he : ε.comp ε.ker.subtype = 0 := by ext x; exact x.property
    rw [← LinearMap.lTensor_comp, he, LinearMap.lTensor_zero]
  have hd : (ε.ker.subtype.lTensor T).comp (π.lTensor T) =
      LinearMap.id - (σ.lTensor T).comp (ε.lTensor T) := by
    rw [← LinearMap.lTensor_comp, subtype_splitEvaluationKernelProjection,
      LinearMap.lTensor_sub, LinearMap.lTensor_id, LinearMap.lTensor_comp]
  constructor
  · intro he
    apply (subsingleton_iff_forall_eq 0).mpr
    intro x
    apply hi
    apply he
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero] using
      LinearMap.congr_fun hz x
  · intro ht
    have hl : Function.LeftInverse (σ.lTensor T) (ε.lTensor T) := by
      intro x
      have hx := LinearMap.congr_fun hd x
      have hp : π.lTensor T x = 0 := Subsingleton.elim _ _
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] at hx
      rw [hp, map_zero] at hx
      exact (sub_eq_zero.mp hx.symm).symm
    exact hl.injective

end FLT.Mazur.Approximation
