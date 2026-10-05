/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.TwistTensorCoherence
public import FLT.GroupScheme.SemilinearTwistPoints

/-!
# Points of the fixed tensor comparison

Evaluation commutes with restriction of equivariant maps and with the tensor
comparison. These identities will identify the descended comultiplication
with the original group law on geometric points.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace SemilinearDescent
universe u
variable {R S H J Ω : Type u} {G : Type*}
  [CommRing R] [CommRing S] [CommRing H] [CommRing J] [CommRing Ω]
  [Algebra R S] [Algebra R H] [Algebra R J] [Algebra R Ω] [Group G]
  (σ : G →* (S ≃ₐ[R] S)) (τ : G →* (H ≃ₐ[R] H))
  (υ : G →* (J ≃ₐ[R] J))

/-- Evaluation of twisted points is natural in an equivariant coordinate map. -/
theorem twistPoint_map (s : S →ₐ[R] Ω) (f : J →ₐ[R] Ω) (q : H →ₐ[R] J)
    (hq : ∀ g x, υ g (q x) = q (τ g x)) :
    (twistPoint σ υ s f).comp (twistMap σ τ υ q hq) = twistPoint σ τ s (f.comp q) := by
  ext x
  change Algebra.TensorProduct.lift s f (fun _ _ ↦ .all _ _)
    (Algebra.TensorProduct.map (AlgHom.id R S) q x.val) =
      Algebra.TensorProduct.lift s (f.comp q) (fun _ _ ↦ .all _ _) x.val
  generalize x.val = z
  induction z using TensorProduct.inductionOn with
  | tmul t h => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Evaluation of joined coordinates is the product of the two evaluations. -/
theorem tensorJoin_evaluate (s : S →ₐ[R] Ω) (f : H →ₐ[R] Ω) (g : J →ₐ[R] Ω)
    (x : S ⊗[R] H) (y : S ⊗[R] J) :
    Algebra.TensorProduct.lift s (Algebra.TensorProduct.lift f g (fun _ _ ↦ .all _ _))
      (fun _ _ ↦ .all _ _) (tensorJoin x y) =
        Algebra.TensorProduct.lift s f (fun _ _ ↦ .all _ _) x *
          Algebra.TensorProduct.lift s g (fun _ _ ↦ .all _ _) y := by
  induction x using TensorProduct.inductionOn with
  | tmul t h =>
    induction y using TensorProduct.inductionOn with
    | tmul u j => simp [tensorJoin, mul_mul_mul_comm]
    | add y z hy hz => simpa [tensorJoin, mul_add] using congrArg₂ (· + ·) hy hz
  | add x z hx hz => simpa [tensorJoin, add_mul] using congrArg₂ (· + ·) hx hz

/-- The fixed tensor comparison preserves pairwise evaluation of points. -/
theorem twistPoint_tensor (s : S →ₐ[R] Ω) (f : H →ₐ[R] Ω) (g : J →ₐ[R] Ω) :
    (twistPoint σ (twistAction τ υ) s
      (Algebra.TensorProduct.lift f g (fun _ _ ↦ .all _ _))).comp
        (twistTensorMap σ τ υ) =
      Algebra.TensorProduct.lift (twistPoint σ τ s f) (twistPoint σ υ s g)
        (fun _ _ ↦ .all _ _) := by
  apply Algebra.TensorProduct.ext'
  intro x y
  exact tensorJoin_evaluate s f g x.val y.val

end SemilinearDescent
