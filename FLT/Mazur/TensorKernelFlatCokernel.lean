/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Nonflat coefficient base change for a kernel with flat cokernel

If the target and cokernel of a linear map are flat, its kernel commutes with
arbitrary tensor coefficients. This criterion applies to a Cech differential
once bounded-complex arguments establish flatness of its cokernel.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.TensorKernelFlatCokernel

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- The kernel of a surjection between flat modules is flat. -/
theorem flat_kernel_of_shortExact [Module.Flat R N] [Module.Flat R P]
    (i : M →ₗ[R] N) (q : N →ₗ[R] P)
    (hi : Function.Injective i) (hq : Function.Surjective q) (he : Function.Exact i q) :
    Module.Flat R M := by
  apply Module.Flat.iff_rTensor_preserves_injective_linearMap.mpr
  intro A B _ _ _ _ g hg
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro x hx
  change x = 0
  have hx0 : g.rTensor M x = 0 := hx
  have hix : i.lTensor A x = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap g hg (M := N)
    rw [map_zero, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, hx0, map_zero]
  exact (LinearMap.lTensor_injective_of_exact_of_flat q hq i hi he A)
    (hix.trans (map_zero _).symm)

/-- A map into a flat module with flat cokernel has flat image. -/
theorem range_flat (f : M →ₗ[R] N) [Module.Flat R N]
    [Module.Flat R (N ⧸ f.range)] : Module.Flat R f.range :=
  flat_kernel_of_shortExact f.range.subtype f.range.mkQ f.range.subtype_injective
    f.range.mkQ_surjective (by intro x; simp)

/-- Tensoring the kernel inclusion remains exact for arbitrary coefficients. -/
theorem kernel_lTensor_exact (f : M →ₗ[R] N)
    [Module.Flat R (N ⧸ f.range)] (A : Type*) [AddCommGroup A] [Module R A] :
    Function.Exact (f.ker.subtype.lTensor A) (f.lTensor A) := by
  have hi := LinearMap.lTensor_injective_of_exact_of_flat f.range.mkQ
    f.range.mkQ_surjective f.range.subtype f.range.subtype_injective
    (by intro x; simp) A
  have he := lTensor_exact A (LinearMap.exact_subtype_ker_map f.rangeRestrict)
    f.surjective_rangeRestrict
  have hker : f.rangeRestrict.ker = f.ker := by ext x; simp
  rw [hker] at he
  have hcomp : (f.range.subtype.lTensor A).comp (f.rangeRestrict.lTensor A) = f.lTensor A := by
    rw [← LinearMap.lTensor_comp]
    rfl
  simpa only [← LinearMap.coe_comp, hcomp] using he.comp_injective _ hi (map_zero _)

/-- The canonical kernel base-change map is bijective even for nonflat coefficients. -/
theorem tensorKer_bijective (f : M →ₗ[R] N) [Module.Flat R N]
    [Module.Flat R (N ⧸ f.range)] (A : Type*) [AddCommGroup A] [Module R A] :
    Function.Bijective (LinearMap.tensorKer R A f) := by
  let _ := range_flat f
  have hi := LinearMap.lTensor_injective_of_exact_of_flat f.rangeRestrict
    f.surjective_rangeRestrict f.ker.subtype f.ker.subtype_injective
    (by intro x; simp [Subtype.ext_iff]) A
  constructor
  · intro x y hxy
    apply hi
    simpa only [LinearMap.tensorKer_coe] using congrArg Subtype.val hxy
  · intro x
    obtain ⟨y, hy⟩ := (kernel_lTensor_exact f A x.val).mp x.property
    exact ⟨y, Subtype.ext (by simpa only [LinearMap.tensorKer_coe] using hy)⟩

end FLT.Mazur.TensorKernelFlatCokernel
