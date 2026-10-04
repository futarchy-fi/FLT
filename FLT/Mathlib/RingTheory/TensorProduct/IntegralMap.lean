/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # Integrality of the tensor map induced by an integral algebra homomorphism -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra.TensorProduct

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]

/-- Extension of scalars preserves integrality of an arbitrary algebra homomorphism. -/
theorem isIntegral_lTensor (f : A →ₐ[R] B) (hf : f.IsIntegral) :
    (lTensor (S := C) C f).IsIntegral := by
  let F : C ⊗[R] A →ₐ[C] C ⊗[R] B := lTensor C f
  have hc : (includeRight : B →ₐ[R] C ⊗[R] B).toRingHom.comp f.toRingHom =
      F.toRingHom.comp (includeRight : A →ₐ[R] C ⊗[R] A).toRingHom := by
    ext a
    simp [F]
  intro x
  induction x with
  | tmul c b =>
    have hb := (hf b).map (includeRight : B →ₐ[R] C ⊗[R] B).toRingHom
    rw [hc] at hb
    have hleft := F.toRingHom.isIntegralElem_map (x := c ⊗ₜ[R] (1 : A))
    simpa [F, tmul_mul_tmul] using RingHom.IsIntegralElem.mul F.toRingHom hleft hb.of_comp
  | add x y hx hy => exact RingHom.IsIntegralElem.add F.toRingHom hx hy

end Algebra.TensorProduct
