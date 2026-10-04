/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.SemilinearTensorTwist

/-!
# Galois transformation of points of a semilinear twist

Coefficient evaluation restricts to the fixed coordinate algebra. Its
transformation law involves the inverse twisting action, for an arbitrary
group, rather than just an involution. This establishes equivariance of the
actual evaluation map without presuming a descended group law.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace SemilinearDescent

universe u
variable {R S H Ω : Type u} {G : Type*}
  [CommRing R] [CommRing S] [CommRing H] [CommRing Ω]
  [Algebra R S] [Algebra R H] [Algebra R Ω] [Group G]
  (σ : G →* (S ≃ₐ[R] S)) (τ : G →* (H ≃ₐ[R] H))

/-- Evaluate the tensor coordinates and restrict to the actual fixed subalgebra. -/
def twistPoint (s : S →ₐ[R] Ω) (f : H →ₐ[R] Ω) : twistModel σ τ →ₐ[R] Ω :=
  (Algebra.TensorProduct.lift s f (fun _ _ ↦ .all _ _)).comp (twistModel σ τ).val

/-- Simultaneous coefficient and coordinate action leaves a descended point unchanged. -/
theorem twistPoint_action (s : S →ₐ[R] Ω) (f : H →ₐ[R] Ω) (g : G) :
    twistPoint σ τ (s.comp (σ g).toAlgHom) (f.comp (τ g).toAlgHom) =
      twistPoint σ τ s f := by
  ext x
  have he (z : S ⊗[R] H) :
      Algebra.TensorProduct.lift (s.comp (σ g).toAlgHom) (f.comp (τ g).toAlgHom)
        (fun _ _ ↦ .all _ _) z =
      Algebra.TensorProduct.lift s f (fun _ _ ↦ .all _ _) (twistAction σ τ g z) := by
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s h => rfl
  exact (he x.val).trans (congrArg (Algebra.TensorProduct.lift s f
    (fun _ _ ↦ .all _ _)) (x.property g))

/-- Target automorphisms act on both the coefficient embedding and the original point. -/
theorem twistPoint_postcomp (s : S →ₐ[R] Ω) (f : H →ₐ[R] Ω) (γ : Ω →ₐ[R] Ω) :
    γ.comp (twistPoint σ τ s f) = twistPoint σ τ (γ.comp s) (γ.comp f) := by
  ext x
  have he (z : S ⊗[R] H) :
      γ (Algebra.TensorProduct.lift s f (fun _ _ ↦ .all _ _) z) =
      Algebra.TensorProduct.lift (γ.comp s) (γ.comp f) (fun _ _ ↦ .all _ _) z := by
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s h => exact map_mul γ _ _
  exact he x.val

/-- The prescribed Galois transformation uses the inverse coordinate action. -/
theorem twistPoint_equivariant (s : S →ₐ[R] Ω) (f : H →ₐ[R] Ω)
    (γ : Ω →ₐ[R] Ω) (g : G) (hγ : γ.comp s = s.comp (σ g).toAlgHom) :
    γ.comp (twistPoint σ τ s f) =
      twistPoint σ τ s ((γ.comp f).comp (τ g⁻¹).toAlgHom) := by
  rw [twistPoint_postcomp, hγ]
  have he : ((γ.comp f).comp (τ g⁻¹).toAlgHom).comp (τ g).toAlgHom = γ.comp f := by
    ext x
    change γ (f (τ g⁻¹ (τ g x))) = γ (f x)
    rw [map_inv]
    exact congrArg (fun y ↦ γ (f y)) ((τ g).symm_apply_apply x)
  rw [← twistPoint_action σ τ s ((γ.comp f).comp (τ g⁻¹).toAlgHom) g, he]

end SemilinearDescent
