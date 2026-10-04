/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.TensorProduct.Basic

/-! # Flat base change of the actual reduction kernel -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace AlgHom
variable {R B C : Type*} (D : Type*) [CommRing R] [CommRing B] [CommRing C]
  [CommRing D] [Algebra R B] [Algebra R C] [Algebra R D]
  [Module.Flat R D] (q : B →ₐ[R] C)

/-- Tensoring the original kernel gives the kernel of the actual base-changed algebra map. -/
def flatReductionKernelEquiv :
    D ⊗[R] RingHom.ker q ≃ₗ[D]
      RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R D) q) :=
  LinearMap.tensorKerEquiv D D q.toLinearMap

/-- The comparison is the canonical inclusion on pure tensors. -/
theorem flatReductionKernelEquiv_tmul (d : D) (b : RingHom.ker q) :
    (flatReductionKernelEquiv D q (d ⊗ₜ[R] b) : D ⊗[R] B) = d ⊗ₜ[R] (b : B) := rfl

/-- Every element of the actual base-changed kernel comes from the original kernel. -/
theorem exists_tensor_reduction_kernel
    (z : RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R D) q)) :
    ∃ w : D ⊗[R] RingHom.ker q,
      (flatReductionKernelEquiv D q w : D ⊗[R] B) = z :=
  ⟨(flatReductionKernelEquiv D q).symm z,
    congrArg Subtype.val ((flatReductionKernelEquiv D q).apply_symm_apply z)⟩

end AlgHom
