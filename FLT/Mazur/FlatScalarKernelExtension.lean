/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Exact scalar kernel ideals under flat extension

The scalar equations of an algebra extend to exactly the scalar equations
of its tensor product with a flat algebra. This is equality of full ideals,
not only of their radicals or zero loci.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FlatScalarKernelExtension
variable {R : Type*} [CommRing R] (B S : Type*) [CommRing B] [CommRing S]
  [Algebra R B] [Algebra R S] [Module.Flat R S]

/-- A flat scalar extension preserves the full scalar equation ideal. -/
theorem scalar_kernel_eq :
    RingHom.ker (algebraMap S (S ⊗[R] B)) =
      (RingHom.ker (algebraMap R B)).map (algebraMap R S) := by
  let f : R →ₗ[R] B := Algebra.linearMap R B
  let I := RingHom.ker (algebraMap R B)
  apply le_antisymm
  · intro x hx
    change x ⊗ₜ[R] (1 : B) = 0 at hx
    have hz : f.lTensor S (x ⊗ₜ[R] (1 : R)) = 0 := by
      simpa only [LinearMap.lTensor_tmul, f, Algebra.linearMap_apply, map_one] using hx
    obtain ⟨z, hz⟩ :=
      (Module.Flat.lTensor_exact S (LinearMap.exact_subtype_ker_map f) _).mp hz
    have hm : ∀ z : S ⊗[R] LinearMap.ker f,
        TensorProduct.rid R S ((LinearMap.ker f).subtype.lTensor S z) ∈
          I.map (algebraMap R S) := by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul t r =>
        change r.val • t ∈ I.map (algebraMap R S)
        rw [Algebra.smul_def, mul_comm]
        exact Ideal.mul_mem_left _ t (Ideal.mem_map_of_mem _ r.property)
      | add z w hz hw =>
        simpa only [map_add] using Ideal.add_mem _ hz hw
    have h := hm z
    rw [hz] at h
    simpa only [TensorProduct.rid_tmul, one_smul] using h
  · apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change algebraMap S (S ⊗[R] B) (algebraMap R S r) = 0
    change algebraMap R S r ⊗ₜ[R] (1 : B) = 0
    rw [Algebra.TensorProduct.tmul_one_eq_one_tmul, hr, tmul_zero]

end FLT.Mazur.FlatScalarKernelExtension
