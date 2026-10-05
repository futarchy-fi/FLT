/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.TwistTensorMaps

/-!
# Triple coherence for fixed tensor comparisons

The two tensor comparisons on a triple agree under the canonical associator.
The identity is proved on the actual invariant subalgebras and involves the
same comparison maps used in effective scalar recovery.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace SemilinearDescent
universe u
variable {R S H J K : Type u} {G : Type*}
  [CommRing R] [CommRing S] [CommRing H] [CommRing J] [CommRing K]
  [Algebra R S] [Algebra R H] [Algebra R J] [Algebra R K] [Group G]
  (σ : G →* (S ≃ₐ[R] S)) (τ : G →* (H ≃ₐ[R] H))
  (υ : G →* (J ≃ₐ[R] J)) (ω : G →* (K ≃ₐ[R] K))

/-- Multiplication of splitting coefficients in a pair of coordinate tensors. -/
def tensorJoin (x : S ⊗[R] H) (y : S ⊗[R] J) : S ⊗[R] (H ⊗[R] J) :=
  Algebra.TensorProduct.map (AlgHom.id R S) Algebra.TensorProduct.includeLeft x *
    Algebra.TensorProduct.map (AlgHom.id R S) Algebra.TensorProduct.includeRight y

/-- Joining three coordinate tensors is associative under the coordinate associator. -/
theorem tensorJoin_assoc (x : S ⊗[R] H) (y : S ⊗[R] J) (z : S ⊗[R] K) :
    Algebra.TensorProduct.map (AlgHom.id R S)
      (Algebra.TensorProduct.assoc R R R H J K).toAlgHom
      (tensorJoin (tensorJoin x y) z) = tensorJoin x (tensorJoin y z) := by
  induction x using TensorProduct.inductionOn with
  | tmul s h =>
    induction y using TensorProduct.inductionOn with
    | tmul t j =>
      induction z using TensorProduct.inductionOn with
      | tmul u k => simp [tensorJoin, mul_assoc]
      | add z w hz hw => simpa [tensorJoin, mul_add] using congrArg₂ (· + ·) hz hw
    | add y w hy hw => simpa [tensorJoin, mul_add, add_mul] using congrArg₂ (· + ·) hy hw
  | add x w hx hw => simpa [tensorJoin, add_mul] using congrArg₂ (· + ·) hx hw

/-- Associating the original coordinate tensors is equivariant. -/
theorem tensorAssoc_equivariant (g : G) (z : (H ⊗[R] J) ⊗[R] K) :
    twistAction τ (twistAction υ ω) g ((Algebra.TensorProduct.assoc R R R H J K) z) =
      (Algebra.TensorProduct.assoc R R R H J K) (twistAction (twistAction τ υ) ω g z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x k =>
    induction x using TensorProduct.inductionOn with
    | tmul h j => rfl
    | add x y hx hy => simpa [TensorProduct.add_tmul] using congrArg₂ (· + ·) hx hy
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The two triple-overlap tensor comparisons agree, including the associator. -/
theorem twistTensorMap_assoc :
    (twistMap σ (twistAction (twistAction τ υ) ω) (twistAction τ (twistAction υ ω))
      (Algebra.TensorProduct.assoc R R R H J K).toAlgHom
      (tensorAssoc_equivariant τ υ ω)).comp
        ((twistTensorMap σ (twistAction τ υ) ω).comp
          (Algebra.TensorProduct.map (twistTensorMap σ τ υ)
            (AlgHom.id R (twistModel σ ω)))) =
      (twistTensorMap σ τ (twistAction υ ω)).comp
        ((Algebra.TensorProduct.map (AlgHom.id R (twistModel σ τ))
          (twistTensorMap σ υ ω)).comp
            (Algebra.TensorProduct.assoc R R R (twistModel σ τ)
              (twistModel σ υ) (twistModel σ ω)).toAlgHom) := by
  apply AlgHom.toLinearMap_injective
  ext x y z
  change Algebra.TensorProduct.map (AlgHom.id R S)
    (Algebra.TensorProduct.assoc R R R H J K).toAlgHom
      (tensorJoin (tensorJoin x.val y.val) z.val) = tensorJoin x.val (tensorJoin y.val z.val)
  exact tensorJoin_assoc x.val y.val z.val

end SemilinearDescent
