/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierDualHopf

/-!
# Pointwise detection of constant group Hopf operations

Evaluations on group elements detect tensors of the dual group algebra. Its
counit and comultiplication read the identity and multiplication of that group.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open HopfAlgebra HopfAlgebra.CartierDual

namespace FLT.Mazur.ConstantGroupTensorEvaluation

universe u
variable (R G : Type u) [CommRing R] [CommGroup G] [Finite G]

/-- Evaluation on a group-like basis element of the original group algebra. -/
def evaluation (g : G) : CartierDual R (MonoidAlgebra R G) →ₐ[R] R :=
  (Pi.evalAlgHom R (fun _ : G => R) g).comp (groupAlgebraEquiv R G).toAlgHom

omit [CommGroup G] [Finite G] in
/-- Coordinate evaluation reads the original group-algebra basis element. -/
@[simp] theorem evaluation_apply (g : G) (φ : CartierDual R (MonoidAlgebra R G)) :
    evaluation R G g φ = φ (MonoidAlgebra.single g 1) := rfl

omit [CommGroup G] in
/-- Tensor evaluation agrees with the canonical dual tensor pairing. -/
theorem tensor_evaluation (g h : G)
    (t : CartierDual R (MonoidAlgebra R G) ⊗[R] CartierDual R (MonoidAlgebra R G)) :
    Algebra.TensorProduct.productMap (evaluation R G g) (evaluation R G h) t =
      tensorEquiv R (MonoidAlgebra R G) (MonoidAlgebra R G) t
        (MonoidAlgebra.single g 1 ⊗ₜ[R] MonoidAlgebra.single h 1) := by
  induction t using TensorProduct.inductionOn with
  | tmul φ ψ => rw [Algebra.TensorProduct.productMap_apply_tmul, tensorEquiv_tmul]; rfl
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

omit [CommGroup G] in
/-- Evaluation on every group pair separates tensors of constant coordinates. -/
theorem tensor_ext {x y :
    CartierDual R (MonoidAlgebra R G) ⊗[R] CartierDual R (MonoidAlgebra R G)}
    (h : ∀ g k, Algebra.TensorProduct.productMap (evaluation R G g) (evaluation R G k) x =
      Algebra.TensorProduct.productMap (evaluation R G g) (evaluation R G k) y) : x = y := by
  apply (tensorEquiv R (MonoidAlgebra R G) (MonoidAlgebra R G)).injective
  apply ((MonoidAlgebra.basis G R).tensorProduct (MonoidAlgebra.basis G R)).ext
  rintro ⟨g, k⟩
  simp only [Module.Basis.tensorProduct_apply, MonoidAlgebra.basis_apply]
  exact (tensor_evaluation R G g k x).symm.trans ((h g k).trans
    (tensor_evaluation R G g k y))

/-- The constant counit reads the identity group element. -/
theorem counit_evaluation (φ : CartierDual R (MonoidAlgebra R G)) :
    Coalgebra.counit (R := R) φ = evaluation R G 1 φ := rfl

/-- Constant comultiplication reads multiplication of the original group elements. -/
theorem comul_evaluation (g h : G) (φ : CartierDual R (MonoidAlgebra R G)) :
    Algebra.TensorProduct.productMap (evaluation R G g) (evaluation R G h)
      (Coalgebra.comul (R := R) φ) = evaluation R G (g * h) φ := by
  rw [tensor_evaluation]
  change tensorEquiv R _ _ (HopfAlgebra.CartierDual.comul φ) _ = _
  rw [comul_eval, MonoidAlgebra.single_mul_single, one_mul]
  rfl

end FLT.Mazur.ConstantGroupTensorEvaluation
