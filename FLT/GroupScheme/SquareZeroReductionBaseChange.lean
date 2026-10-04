/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FlatReductionKernel

/-! # Square-zero thickenings after base change -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace AlgHom
variable {R B C : Type*} (D : Type*) [CommRing R] [CommRing B] [CommRing C]
  [CommRing D] [Algebra R B] [Algebra R C] [Algebra R D]
  (q : B →ₐ[R] C)

/-- Surjectivity of the actual reduction is preserved by tensor base change. -/
theorem tensor_reduction_surjective (hq : Function.Surjective q) :
    Function.Surjective (Algebra.TensorProduct.map (AlgHom.id R D) q) :=
  Algebra.TensorProduct.map_surjective _ _ Function.surjective_id hq

/-- A surjective square-zero reduction remains square-zero under arbitrary base change. -/
theorem squareZero_tensor_reduction (hq : Function.Surjective q)
    (hJ : RingHom.ker q ^ 2 = ⊥) :
    RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R D) q) ^ 2 = ⊥ := by
  rw [Algebra.TensorProduct.lTensor_ker q hq, ← Ideal.map_pow, hJ, Ideal.map_bot]

/-- Flat base change preserves a specified natural-number annihilator of the kernel. -/
theorem nsmul_tensor_reduction_kernel [Module.Flat R D] (N : ℕ)
    (hN : ∀ b ∈ RingHom.ker q, N • b = 0)
    (z : RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R D) q)) :
    N • (z : D ⊗[R] B) = 0 := by
  obtain ⟨w, hw⟩ := exists_tensor_reduction_kernel D q z
  rw [← hw]
  clear hw z
  induction w using TensorProduct.inductionOn with
  | tmul d b =>
    rw [flatReductionKernelEquiv_tmul, ← TensorProduct.tmul_smul, hN b b.property,
      TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, Submodule.coe_add, nsmul_add, hx, hy, add_zero]

end AlgHom
