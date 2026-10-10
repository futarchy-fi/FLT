/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorKernelExtension
public import Mathlib.RingTheory.Flat.Tensor

/-!
# Flat cokernels from injectivity on ideal quotients

A map into a flat module has flat cokernel if it stays injective after tensoring
with every quotient of the base ring by an ideal. The diagram chase uses the
actual quotient map and tensor right exactness, without assuming cokernel flatness.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FlatCokernelResidueIdeals
open TensorKernelExtension
variable {R M N Q : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup Q] [Module R Q] [Module.Flat R N]

/-- Injectivity on all ideal quotients makes an actual cokernel flat. -/
theorem flat_of_quotient_injective (f : M →ₗ[R] N) (q : N →ₗ[R] Q)
    (he : Function.Exact f q) (hq : Function.Surjective q)
    (h : ∀ I : Ideal R, Function.Injective (f.lTensor (R ⧸ I))) :
    Module.Flat R Q := by
  apply Module.Flat.iff_rTensor_injective'.mpr
  intro I
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro z hz
  change z = 0
  obtain ⟨t, rfl⟩ := LinearMap.lTensor_surjective I hq z
  have ht : q.lTensor R (I.subtype.rTensor N t) = 0 := by
    rw [differential_naturality]
    exact hz
  obtain ⟨u, hu⟩ := (lTensor_exact R he hq _).mp ht
  have hu0 : I.mkQ.rTensor M u = 0 := by
    apply h I
    rw [map_zero, differential_naturality, hu]
    exact (rTensor_exact N (LinearMap.exact_subtype_mkQ I)
      I.mkQ_surjective).apply_apply_eq_zero t
  obtain ⟨v, hv⟩ := (rTensor_exact M (LinearMap.exact_subtype_mkQ I)
    I.mkQ_surjective u).mp hu0
  have htv : t = f.lTensor I v := by
    apply Module.Flat.rTensor_preserves_injective_linearMap I.subtype I.subtype_injective
    rw [← differential_naturality, hv, hu]
  rw [htv]
  exact (lTensor_exact I he hq).apply_apply_eq_zero v

/-- The quotient by the actual image is flat under the ideal-quotient test. -/
theorem range_quotient_flat (f : M →ₗ[R] N)
    (h : ∀ I : Ideal R, Function.Injective (f.lTensor (R ⧸ I))) :
    Module.Flat R (N ⧸ f.range) :=
  flat_of_quotient_injective f f.range.mkQ (LinearMap.exact_map_mkQ_range f)
    f.range.mkQ_surjective h

end FLT.Mazur.FlatCokernelResidueIdeals
