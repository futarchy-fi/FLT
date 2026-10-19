/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlat

/-!
# Cocommutativity of the actual equivariant-function Hopf algebra

Swapping tensor factors swaps the original labels. Commutativity of label addition
therefore makes the descended comultiplication cocommutative.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace GaloisModule.GenericFiber

variable (K L A : Type) [Field K] [Field L] [Algebra K L]
  [IsGalois K L] [IsSepClosed L] [AddCommGroup A] [DistribMulAction (L ≃ₐ[K] L) A]
  [Finite A] [ContinuousSMulDiscrete (L ≃ₐ[K] L) A]

attribute [local instance] hopfAlgebra

/-- Swapping the original tensor coordinates swaps their original labels. -/
theorem tensorEquiv_comm_eval
    (z : (A →[L ≃ₐ[K] L] L) ⊗[K] (A →[L ≃ₐ[K] L] L)) (x y : A) :
    tensorEquiv K L A A (TensorProduct.comm K _ _ z) (x, y) =
      tensorEquiv K L A A z (y, x) := by
  induction z using TensorProduct.inductionOn with
  | tmul f g =>
    simp only [TensorProduct.comm_tmul, tensorEquiv_tmul]
    exact mul_comm _ _
  | add a b ha hb =>
    simp only [map_add]
    change tensorEquiv K L A A (TensorProduct.comm K _ _ a) (x, y) +
      tensorEquiv K L A A (TensorProduct.comm K _ _ b) (x, y) =
        tensorEquiv K L A A a (y, x) + tensorEquiv K L A A b (y, x)
    exact congrArg₂ (· + ·) ha hb

/-- The existing descended Hopf algebra is cocommutative because label addition is commutative. -/
instance equivariantHopf_cocomm :
    Coalgebra.IsCocomm K (A →[L ≃ₐ[K] L] L) where
  comm_comp_comul := by
    apply LinearMap.ext
    intro f
    apply (tensorEquiv K L A A).injective
    ext xy
    change tensorEquiv K L A A (TensorProduct.comm K _ _ (comulAlgHom K L A f)) xy =
      tensorEquiv K L A A (comulAlgHom K L A f) xy
    obtain ⟨x, y⟩ := xy
    rw [tensorEquiv_comm_eval, comulAlgHom_eval, comulAlgHom_eval,
      add_comm]

end GaloisModule.GenericFiber
