/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Changing the coefficient algebra of a tensor product

An equivalence of coefficient algebras identifies scalar extensions
semilinearly over that exact equivalence.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.TensorAlgebraSemilinearEquiv

open TensorProduct

variable {A C D : Type*} [CommRing A] [CommRing C] [CommRing D]
  [Algebra A C] [Algebra A D] (e : C ≃ₐ[A] D)
  (M : Type*) [AddCommGroup M] [Module A M]

/-- The forward and reverse coefficient maps are inverse. -/
instance forwardInverse : RingHomInvPair e.toRingHom e.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv e.toRingEquiv

/-- The reverse and forward coefficient maps are inverse. -/
instance reverseInverse : RingHomInvPair e.symm.toRingHom e.toRingHom :=
  RingHomInvPair.of_ringEquiv e.symm.toRingEquiv

/-- Change coefficient algebras, retaining their full semilinear actions. -/
def equiv : LinearEquiv e.toRingHom (σ' := e.symm.toRingHom)
    (C ⊗[A] M) (D ⊗[A] M) :=
  { (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl A M)).toAddEquiv with
    map_smul' := fun c x ↦ by
      change TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl A M) (c • x) =
        e c • TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl A M) x
      induction x using TensorProduct.inductionOn with
      | tmul d m =>
        change e (c * d) ⊗ₜ[A] m = e c • (e d ⊗ₜ[A] m)
        rw [map_mul, smul_tmul', smul_eq_mul]
      | add x y hx hy => simp only [smul_add, map_add, hx, hy] }

/-- The coefficient comparison acts on pure tensors by the given algebra equivalence. -/
@[simp] theorem equiv_tmul (c : C) (m : M) :
    equiv e M (c ⊗ₜ[A] m) = e c ⊗ₜ[A] m := rfl

end FLT.Mazur.TensorAlgebraSemilinearEquiv
