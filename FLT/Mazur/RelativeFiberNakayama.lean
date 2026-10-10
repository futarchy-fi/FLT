/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorKernelFlatCokernel
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Nakayama detection over a coefficient fiber

The module need only be finite over the ambient algebra, not over the base.
Vanishing after a coefficient quotient is detected when the extended base
ideal lies in the Jacobson radical. A surjection to a base-flat finitely
presented module is then an isomorphism if it is injective on that fiber.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FCurve

variable {R B M N : Type*} [CommRing R] [CommRing B] [Algebra R B]
  [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M]
  [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]

/-- Relative Nakayama: finiteness over the ambient algebra detects a zero fiber. -/
theorem subsingleton_of_coefficient_fiber (J : Ideal R)
    (hJ : J.map (algebraMap R B) ≤ Ideal.jacobson ⊥) [Module.Finite B M]
    [Subsingleton ((R ⧸ J) ⊗[R] M)] : Subsingleton M := by
  have hm (x : M) : x ∈ J • (⊤ : Submodule R M) := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    have h := congrArg (quotTensorEquivQuotSMul M J)
      (Subsingleton.elim (1 ⊗ₜ[R] x : (R ⧸ J) ⊗[R] M) 0)
    simpa only [quotTensorEquivQuotSMul_mk_one_tmul, map_zero] using h
  have htop : (⊤ : Submodule B M) ≤ ⊥ := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hJ
    rw [bot_sup_eq]
    intro x _
    change x ∈ (J.map (algebraMap R B) • (⊤ : Submodule B M)).restrictScalars R
    rw [Ideal.smul_restrictScalars]
    exact hm x
  exact (Submodule.subsingleton_iff B).mp (subsingleton_of_bot_eq_top (bot_le.antisymm htop))

/-- Surjectivity on a coefficient fiber lifts for a finite target. -/
theorem surjective_of_coefficient_fiber (J : Ideal R)
    (hJ : J.map (algebraMap R B) ≤ Ideal.jacobson ⊥)
    (f : M →ₗ[B] N) [Module.Finite B N]
    (hf : Function.Surjective ((f.restrictScalars R).lTensor (R ⧸ J))) :
    Function.Surjective f := by
  let q := f.range.mkQ.restrictScalars R
  have he := lTensor_exact (R ⧸ J)
    (LinearMap.exact_map_mkQ_range (f.restrictScalars R)) f.range.mkQ_surjective
  have hz (x : (R ⧸ J) ⊗[R] (N ⧸ f.range)) : x = 0 := by
    obtain ⟨y, rfl⟩ := q.lTensor_surjective (R ⧸ J) f.range.mkQ_surjective x
    exact (he y).mpr (hf y)
  let _ : Subsingleton ((R ⧸ J) ⊗[R] (N ⧸ f.range)) :=
    ⟨fun x y ↦ (hz x).trans (hz y).symm⟩
  let _ : Subsingleton (N ⧸ f.range) := subsingleton_of_coefficient_fiber J hJ
  exact LinearMap.range_eq_top.mp (Submodule.Quotient.subsingleton_iff.mp inferInstance)

/-- A surjection with flat target lifts fiber injectivity if its kernel is finite. -/
theorem injective_of_coefficient_fiber (J : Ideal R)
    (hJ : J.map (algebraMap R B) ≤ Ideal.jacobson ⊥)
    (f : M →ₗ[B] N) (hf : Function.Surjective f) [Module.Flat R N]
    [Module.Finite B f.ker]
    (hfi : Function.Injective ((f.restrictScalars R).lTensor (R ⧸ J))) :
    Function.Injective f := by
  let i := f.ker.subtype.restrictScalars R
  have hi : Function.Injective (i.lTensor (R ⧸ J)) :=
    LinearMap.lTensor_injective_of_exact_of_flat (f.restrictScalars R) hf i
      f.ker.subtype_injective (LinearMap.exact_subtype_ker_map f) (R ⧸ J)
  have he := lTensor_exact (R ⧸ J) (LinearMap.exact_subtype_ker_map
    (f.restrictScalars R)) hf
  have hz (x : (R ⧸ J) ⊗[R] f.ker) : x = 0 := by
    apply hi
    rw [map_zero]
    apply hfi
    rw [map_zero]
    exact (he _).mpr ⟨x, rfl⟩
  let _ : Subsingleton ((R ⧸ J) ⊗[R] f.ker) :=
    ⟨fun x y ↦ (hz x).trans (hz y).symm⟩
  let _ : Subsingleton f.ker := subsingleton_of_coefficient_fiber J hJ
  exact LinearMap.ker_eq_bot.mp (Submodule.subsingleton_iff_eq_bot.mp inferInstance)

/-- Finite presentation supplies the finite kernel needed for fiberwise detection. -/
theorem bijective_of_coefficient_fiber (J : Ideal R)
    (hJ : J.map (algebraMap R B) ≤ Ideal.jacobson ⊥)
    (f : M →ₗ[B] N) (hf : Function.Surjective f)
    [Module.Finite B M] [Module.FinitePresentation B N] [Module.Flat R N]
    (hfi : Function.Injective ((f.restrictScalars R).lTensor (R ⧸ J))) :
    Function.Bijective f := by
  let _ : Module.Finite B f.ker := .of_fg (Module.FinitePresentation.fg_ker f hf)
  exact ⟨injective_of_coefficient_fiber J hJ f hf hfi, hf⟩

end FLT.Mazur.FCurve
