/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Flat.Basic

/-!
# Injectivity after killing a kernel by flat extension

Exactness identifies the kernel after a flat extension with the image of the
old kernel. It suffices that old kernel elements become zero in the extension;
the original linear map need not be injective.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FlatExtensionKernelAnnihilation
variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (S : Type*) [CommRing S] [Algebra R S] [Module.Flat R S]

/-- A flat extension is injective once it kills the original kernel generators. -/
theorem lTensor_injective (f : M →ₗ[R] N)
    (h : ∀ z : f.ker, (1 : S) ⊗ₜ[R] z.val = 0) :
    Function.Injective (f.lTensor S) := by
  have hz : f.ker.subtype.lTensor S = 0 := by
    ext s z
    change s ⊗ₜ[R] z.val = 0
    have hs : s ⊗ₜ[R] z.val = s • ((1 : S) ⊗ₜ[R] z.val) := by
      rw [smul_tmul', smul_eq_mul, mul_one]
    rw [hs, h, smul_zero]
  have he := Module.Flat.lTensor_exact S (LinearMap.exact_subtype_ker_map f)
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.exact_iff] at he
  rw [he, hz, LinearMap.range_zero]

end FLT.Mazur.FlatExtensionKernelAnnihilation
