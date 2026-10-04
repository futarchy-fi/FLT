/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.SemilinearScalarRecovery
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Tensor comparison after extending coefficients

Two scalar extensions tensor over the splitting ring by multiplying their
coefficients. These explicit equivalences will detect isomorphisms between
fixed tensor algebras by faithful flatness.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace SemilinearDescent
universe u
variable (R S H J : Type u) [CommRing R] [CommRing S] [CommRing H] [CommRing J]
  [Algebra R S] [Algebra R H] [Algebra R J]

/-- Tensoring two scalar extensions multiplies their splitting coefficients. -/
def scalarTensorEquiv : (S ⊗[R] H) ⊗[S] (S ⊗[R] J) ≃ₐ[S] S ⊗[R] (H ⊗[R] J) :=
  (Algebra.TensorProduct.tensorTensorTensorComm R R S S S H S J).trans
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.lid S S) AlgEquiv.refl)

/-- The scalar tensor comparison on pure tensors. -/
theorem scalarTensorEquiv_tmul (s t : S) (x : H) (y : J) :
    scalarTensorEquiv R S H J ((s ⊗ₜ[R] x) ⊗ₜ[S] (t ⊗ₜ[R] y)) =
      (s * t) ⊗ₜ[R] (x ⊗ₜ[R] y) := by
  simp [scalarTensorEquiv]

/-- Its inverse places the coefficient in the first factor. -/
theorem scalarTensorEquiv_symm_tmul (s : S) (x : H) (y : J) :
    (scalarTensorEquiv R S H J).symm (s ⊗ₜ[R] (x ⊗ₜ[R] y)) =
      (s ⊗ₜ[R] x) ⊗ₜ[S] (1 ⊗ₜ[R] y) := by
  apply (scalarTensorEquiv R S H J).injective
  simp [scalarTensorEquiv_tmul]

/-- On arbitrary tensor factors the comparison is the product of their inclusions. -/
theorem scalarTensorEquiv_product (x : S ⊗[R] H) (y : S ⊗[R] J) :
    scalarTensorEquiv R S H J (x ⊗ₜ[S] y) =
      Algebra.TensorProduct.map (AlgHom.id R S) Algebra.TensorProduct.includeLeft x *
      Algebra.TensorProduct.map (AlgHom.id R S) Algebra.TensorProduct.includeRight y := by
  induction x using TensorProduct.inductionOn with
  | tmul s h =>
    induction y using TensorProduct.inductionOn with
    | tmul t j => simp [scalarTensorEquiv_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, mul_add, hy, hz]
  | add x z hx hz => simp only [TensorProduct.add_tmul, map_add, add_mul, hx, hz]

variable {R S H J}

/-- A map of algebras is bijective if its scalar extension is, over a faithful flat base. -/
theorem bijective_of_scalar_map [Module.FaithfullyFlat R S] (f : H →ₐ[R] J)
    (hf : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R S) f)) :
    Function.Bijective f :=
  (Module.FaithfullyFlat.lTensor_bijective_iff_bijective R S f.toLinearMap).mp hf

end SemilinearDescent
