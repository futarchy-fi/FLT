/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.SemilinearTensorTwist

/-!
# Tensor comparison maps for fixed twist algebras

The comparison multiplies the two splitting coefficients and retains the two
coordinate factors. It restricts to the actual fixed algebras, without any
assumption about invertibility of the group order.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace SemilinearDescent
universe u
variable {R S H J : Type u} {G : Type*}
  [CommRing R] [CommRing S] [CommRing H] [CommRing J]
  [Algebra R S] [Algebra R H] [Algebra R J] [Group G]
  (σ : G →* (S ≃ₐ[R] S)) (τ : G →* (H ≃ₐ[R] H))
  (υ : G →* (J ≃ₐ[R] J))

/-- Scalar extension of an equivariant coordinate map is equivariant. -/
theorem twistMap_equivariant (f : H →ₐ[R] J)
    (hf : ∀ g x, υ g (f x) = f (τ g x)) (g : G) (z : S ⊗[R] H) :
    twistAction σ υ g (Algebra.TensorProduct.map (AlgHom.id R S) f z) =
      Algebra.TensorProduct.map (AlgHom.id R S) f (twistAction σ τ g z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s x => simp only [Algebra.TensorProduct.map_tmul, twistAction_tmul, hf, AlgHom.id_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Restriction of an equivariant coordinate map to its twist. -/
def twistMap (f : H →ₐ[R] J) (hf : ∀ g x, υ g (f x) = f (τ g x)) :
    twistModel σ τ →ₐ[R] twistModel σ υ :=
  fixedMap (twistAction σ τ) (twistAction σ υ)
    (Algebra.TensorProduct.map (AlgHom.id R S) f) (twistMap_equivariant σ τ υ f hf)

/-- The left coordinates embed equivariantly into the tensor coordinates. -/
theorem tensorLeft_equivariant (g : G) (x : H) :
    twistAction τ υ g ((Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] J) x) =
      (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] J) (τ g x) := by
  change τ g x ⊗ₜ[R] υ g 1 = τ g x ⊗ₜ[R] 1
  rw [map_one]

/-- The right coordinates embed equivariantly into the tensor coordinates. -/
theorem tensorRight_equivariant (g : G) (x : J) :
    twistAction τ υ g ((Algebra.TensorProduct.includeRight : J →ₐ[R] H ⊗[R] J) x) =
      Algebra.TensorProduct.includeRight (υ g x) := by
  change τ g 1 ⊗ₜ[R] υ g x = 1 ⊗ₜ[R] υ g x
  rw [map_one]

/-- The tensor comparison between the actual fixed coordinate algebras. -/
def twistTensorMap : twistModel σ τ ⊗[R] twistModel σ υ →ₐ[R]
    twistModel σ (twistAction τ υ) :=
  Algebra.TensorProduct.lift
    (twistMap σ τ (twistAction τ υ) Algebra.TensorProduct.includeLeft
      (tensorLeft_equivariant τ υ))
    (twistMap σ υ (twistAction τ υ) Algebra.TensorProduct.includeRight
      (tensorRight_equivariant τ υ)) (fun _ _ ↦ .all _ _)

/-- On pure tensors the comparison is the product of the two coordinate inclusions. -/
theorem twistTensorMap_tmul (x : twistModel σ τ) (y : twistModel σ υ) :
    (twistTensorMap σ τ υ (x ⊗ₜ[R] y)).val =
      Algebra.TensorProduct.map (AlgHom.id R S) Algebra.TensorProduct.includeLeft x.val *
      Algebra.TensorProduct.map (AlgHom.id R S) Algebra.TensorProduct.includeRight y.val := rfl

end SemilinearDescent
