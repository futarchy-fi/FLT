/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Flat tensor products preserve simultaneous fixed points

A finite family of linear endomorphisms has its simultaneous fixed submodule
as the kernel of the product of their differences from the identity. Flat
exactness and the finite-product tensor comparison identify the base-changed
fixed submodule, without dividing by the number of endomorphisms.
-/

@[expose] public noncomputable section

open TensorProduct

namespace FLT.Mazur.FlatTensorFixed

variable {R I M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (σ : I → M →ₗ[R] M)

/-- The product of the differences from the identity. -/
def difference : M →ₗ[R] (I → M) := LinearMap.pi fun i ↦ σ i - LinearMap.id

/-- The genuine submodule of simultaneous fixed points. -/
def fixed : Submodule R M := LinearMap.ker (difference σ)

/-- Membership in the kernel is precisely simultaneous invariance. -/
lemma mem_fixed (x : M) : x ∈ fixed σ ↔ ∀ i, σ i x = x := by
  change (fun i ↦ σ i x - x) = 0 ↔ _
  simp only [funext_iff, Pi.zero_apply, sub_eq_zero]

variable (N : Type*) [AddCommGroup N] [Module R N]

/-- Finite-product coordinates of the tensor difference map. -/
lemma tensor_difference_apply (x : N ⊗[R] M) (i : I) :
    TensorProduct.piRightHom R R N (fun _ : I ↦ M)
      ((difference σ).lTensor N x) i = (σ i).lTensor N x - x := by
  induction x using TensorProduct.inductionOn with
  | tmul n m =>
      simp only [LinearMap.lTensor_tmul, difference, LinearMap.pi_apply,
        LinearMap.sub_apply, LinearMap.id_apply, TensorProduct.piRightHom_tmul,
        TensorProduct.tmul_sub]
  | add x y hx hy =>
      simp only [map_add, Pi.add_apply, hx, hy]
      abel

variable [Finite I]

/-- Vanishing of the tensor difference is exactly invariance after tensoring. -/
lemma tensor_difference_eq_zero_iff (x : N ⊗[R] M) :
    (difference σ).lTensor N x = 0 ↔ ∀ i, (σ i).lTensor N x = x := by
  classical
  let _ := Fintype.ofFinite I
  rw [← (TensorProduct.piRight R R N (fun _ : I ↦ M)).map_eq_zero_iff]
  change TensorProduct.piRightHom R R N (fun _ : I ↦ M)
    ((difference σ).lTensor N x) = 0 ↔ _
  simp only [funext_iff, tensor_difference_apply, Pi.zero_apply, sub_eq_zero]

variable [Module.Flat R N]

/-- Every fixed tensor lifts uniquely from the tensor product of the fixed submodule. -/
theorem existsUnique_fixed_lift (x : N ⊗[R] M)
    (hx : ∀ i, (σ i).lTensor N x = x) :
    ∃! y : N ⊗[R] fixed σ, (fixed σ).subtype.lTensor N y = x := by
  have he := Module.Flat.lTensor_exact N (LinearMap.exact_subtype_ker_map (difference σ))
  obtain ⟨y, hy⟩ := (he x).mp ((tensor_difference_eq_zero_iff σ N x).mpr hx)
  refine ⟨y, hy, fun z hz ↦ ?_⟩
  exact Module.Flat.lTensor_preserves_injective_linearMap (fixed σ).subtype
    Subtype.val_injective (hz.trans hy.symm)

/-- A tensor lies in the fixed-submodule image exactly when all tensor actions fix it. -/
theorem mem_tensor_fixed_range (x : N ⊗[R] M) :
    x ∈ LinearMap.range ((fixed σ).subtype.lTensor N) ↔
      ∀ i, (σ i).lTensor N x = x := by
  rw [← tensor_difference_eq_zero_iff σ N x]
  exact (Module.Flat.lTensor_exact N
    (LinearMap.exact_subtype_ker_map (difference σ)) x).symm

end FLT.Mazur.FlatTensorFixed
