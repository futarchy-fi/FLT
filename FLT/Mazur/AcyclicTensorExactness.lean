/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorKernelFlatCokernel

/-!
# Tensor exactness with a flat outgoing cokernel

An exact pair remains exact after arbitrary tensor coefficients when the
outgoing differential has flat cokernel. No flatness of the coefficients is
needed. Bounded acyclic flat complexes provide this cokernel condition.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.TensorKernelFlatCokernel

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- Arbitrary tensor coefficients preserve an exact pair with flat outgoing cokernel. -/
theorem lTensor_exact_of_cokernel_flat (d : M →ₗ[R] N) (e : N →ₗ[R] P)
    (he : Function.Exact d e) [Module.Flat R (P ⧸ e.range)]
    (A : Type*) [AddCommGroup A] [Module R A] :
    Function.Exact (d.lTensor A) (e.lTensor A) := by
  have he' : Function.Exact d e.rangeRestrict := by
    intro x
    rw [Subtype.ext_iff]
    exact he x
  have ht := lTensor_exact A he' e.surjective_rangeRestrict
  have hi := LinearMap.lTensor_injective_of_exact_of_flat e.range.mkQ
    e.range.mkQ_surjective e.range.subtype e.range.subtype_injective
    (by intro x; simp) A
  have hc : (e.range.subtype.lTensor A).comp (e.rangeRestrict.lTensor A) = e.lTensor A := by
    rw [← LinearMap.lTensor_comp]
    rfl
  simpa only [← LinearMap.coe_comp, hc] using ht.comp_injective _ hi (map_zero _)

end FLT.Mazur.TensorKernelFlatCokernel
