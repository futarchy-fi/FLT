/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Coalgebra.CoassocSimps

/-!
# Coaction laws descend along compatible linear maps

These tensor identities transfer coalgebra coassociativity to a quotient
coaction without assuming the resulting homogeneous projections.
-/

@[expose] public section
open scoped TensorProduct
namespace Coalgebra

variable {R A H M : Type*} [CommRing R] [AddCommGroup A] [Module R A] [Coalgebra R A]
  [AddCommGroup H] [Module R H] [AddCommGroup M] [Module R M]
  (φ : A →ₗ[R] M) (q : A →ₗ[R] H) (ρ : M →ₗ[R] M ⊗[R] H)
  (δ : H →ₗ[R] H ⊗[R] H)
  (hρ : ρ ∘ₗ φ = TensorProduct.map φ q ∘ₗ comul)
  (hδ : δ ∘ₗ q = TensorProduct.map q q ∘ₗ comul)

include hρ hδ in
/-- Coassociativity holds on the image of any compatible map. -/
theorem coaction_coassoc_on_image (a : A) :
    TensorProduct.assoc R M H H (ρ.rTensor H (ρ (φ a))) =
      δ.lTensor M (ρ (φ a)) := by
  have he : (TensorProduct.assoc R M H H).toLinearMap ∘ₗ ρ.rTensor H ∘ₗ ρ ∘ₗ φ =
      δ.lTensor M ∘ₗ ρ ∘ₗ φ := by
    calc
      _ = (TensorProduct.assoc R M H H).toLinearMap ∘ₗ
          TensorProduct.map (ρ ∘ₗ φ) q ∘ₗ comul := by
        rw [hρ]
        simp only [coassoc_simps, hρ]
      _ = TensorProduct.map φ (TensorProduct.map q q) ∘ₗ
          (TensorProduct.assoc R A A A).toLinearMap ∘ₗ
          (comul (R := R)).rTensor A ∘ₗ comul := by
        rw [hρ]
        simp only [coassoc_simps]
      _ = TensorProduct.map φ (TensorProduct.map q q) ∘ₗ
          (comul (R := R)).lTensor A ∘ₗ comul := by rw [coassoc]
      _ = TensorProduct.map φ (δ ∘ₗ q) ∘ₗ comul := by
        rw [hδ]
        simp only [coassoc_simps]
      _ = _ := by
        rw [hρ]
        simp only [coassoc_simps]
  exact LinearMap.congr_fun he a

include hρ in
/-- Counitality also transfers on the image of a compatible map. -/
theorem coaction_counit_on_image (ε : H →ₗ[R] R) (hε : ε ∘ₗ q = counit) (a : A) :
    TensorProduct.rid R M (ε.lTensor M (ρ (φ a))) = φ a := by
  have he : ε.lTensor M ∘ₗ ρ ∘ₗ φ = TensorProduct.map φ counit ∘ₗ comul := by
    rw [hρ]
    simp only [coassoc_simps, hε]
  rw [CoassocSimps.map_counit_comp_comul_right] at he
  have h := congrArg (TensorProduct.rid R M) (LinearMap.congr_fun he a)
  simpa using h

end Coalgebra
