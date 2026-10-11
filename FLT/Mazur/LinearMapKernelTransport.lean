/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Transporting a kernel through an isomorphism of two-term complexes

A commuting square with invertible vertical maps gives an explicit kernel
equivalence. This keeps the map on the underlying source module visible.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.LinearMapKernelTransport

variable {R M N M' N' : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
  (f : M →ₗ[R] N) (g : M' →ₗ[R] N') (e : M ≃ₗ[R] M') (d : N ≃ₗ[R] N')
  (h : d.toLinearMap.comp f = g.comp e.toLinearMap)

include h in
/-- The kernel is the preimage of the transported kernel under the source equivalence. -/
theorem ker_eq_comap : LinearMap.ker f = (LinearMap.ker g).comap e.toLinearMap := by
  rw [← LinearMap.ker_comp, ← h]
  exact (LinearMap.ker_comp_of_ker_eq_bot _ d.ker).symm

/-- A commuting square of linear equivalences induces an equivalence of the actual kernels. -/
def equiv : LinearMap.ker f ≃ₗ[R] LinearMap.ker g :=
  LinearEquiv.ofEq _ _ (ker_eq_comap f g e d h) ≪≫ₗ e.ofSubmodule' (LinearMap.ker g)

/-- Kernel transport retains the original source equivalence. -/
theorem equiv_apply (x : LinearMap.ker f) :
    (equiv f g e d h x).val = e x.val := rfl

/-- The inverse kernel transport retains the inverse source equivalence. -/
theorem equiv_symm_apply (x : LinearMap.ker g) :
    ((equiv f g e d h).symm x).val = e.symm x.val := rfl

end FLT.Mazur.LinearMapKernelTransport
