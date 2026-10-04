/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Coefficient projectors for a diagonal coalgebra coaction

The projectors are extracted from the coaction. Their homogeneous image follows
from coassociativity, and their sum is the identity by the counit law.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace CoactionBasis

variable {R H M : Type*} [CommRing R] [AddCommGroup H] [Module R H]
  [AddCommGroup M] [Module R M] {ι : Type*} (b : Module.Basis ι R H)

/-- Extract a tensor coefficient in the specified basis. -/
def coefficient (i : ι) : M ⊗[R] H →ₗ[R] M :=
  (TensorProduct.rid R M).toLinearMap ∘ₗ (b.coord i).lTensor M

@[simp] theorem coefficient_tmul (i : ι) (x : M) (h : H) :
    coefficient b i (x ⊗ₜ[R] h) = b.repr h i • x := by
  simp [coefficient]

/-- The diagonal comultiplication in a group-like basis. -/
def diagonal : H →ₗ[R] H ⊗[R] H :=
  b.constr R fun i ↦ b i ⊗ₜ[R] b i

@[simp] theorem diagonal_basis (i : ι) : diagonal b (b i) = b i ⊗ₜ[R] b i := by
  simp [diagonal]

/-- The counit taking each basis vector to one. -/
def augmentation : H →ₗ[R] R := b.constr R fun _ ↦ 1

@[simp] theorem augmentation_basis (i : ι) : augmentation b (b i) = 1 := by
  simp [augmentation]

/-- The degree projector is a coefficient of the actual coaction. -/
def projector (ρ : M →ₗ[R] M ⊗[R] H) (i : ι) : M →ₗ[R] M :=
  coefficient b i ∘ₗ ρ

/-- Coassociativity forces the extracted coefficient to be homogeneous. -/
theorem projector_homogeneous (ρ : M →ₗ[R] M ⊗[R] H)
    (hcoassoc : ∀ x, (TensorProduct.assoc R M H H)
      (ρ.rTensor H (ρ x)) = (diagonal b).lTensor M (ρ x)) (i : ι) (x : M) :
    ρ (projector b ρ i x) = projector b ρ i x ⊗ₜ[R] b i := by
  classical
  have h := congrArg
    (coefficient b (M := M ⊗[R] H) i ∘ (TensorProduct.assoc R M H H).symm)
    (hcoassoc x)
  have hl : ∀ z : M ⊗[R] H,
      coefficient b i (ρ.rTensor H z) = ρ (coefficient b i z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul m h => simp
    | add z w hz hw => simp_all
  have hr : ∀ z : M ⊗[R] H,
      coefficient b i ((TensorProduct.assoc R M H H).symm
        ((diagonal b).lTensor M z)) = coefficient b i z ⊗ₜ[R] b i := by
    have he : coefficient b (M := M ⊗[R] H) i ∘ₗ
        (TensorProduct.assoc R M H H).symm.toLinearMap ∘ₗ (diagonal b).lTensor M =
        ((TensorProduct.mk R M H).flip (b i)) ∘ₗ coefficient b i := by
      apply TensorProduct.ext
      apply LinearMap.ext
      intro m
      apply b.ext
      intro j
      by_cases hji : j = i
      · subst j; simp
      · simp [Ne.symm hji]
    exact LinearMap.congr_fun he
  simpa only [Function.comp_apply, LinearEquiv.symm_apply_apply, hl, hr,
    projector, LinearMap.comp_apply] using h

open Classical in
/-- On a homogeneous element a projector is the Kronecker delta. -/
theorem projector_of_homogeneous (ρ : M →ₗ[R] M ⊗[R] H) (i j : ι) (x : M)
    (hx : ρ x = x ⊗ₜ[R] b j) : projector b ρ i x = if j = i then x else 0 := by
  classical
  by_cases hji : j = i
  · subst j; simp [projector, hx]
  · simp [projector, hx, hji, Ne.symm hji]

open Classical in
/-- Extracted projectors are mutually orthogonal and idempotent. -/
theorem projector_projector (ρ : M →ₗ[R] M ⊗[R] H)
    (hcoassoc : ∀ x, (TensorProduct.assoc R M H H)
      (ρ.rTensor H (ρ x)) = (diagonal b).lTensor M (ρ x)) (i j : ι) (x : M) :
    projector b ρ i (projector b ρ j x) = if j = i then projector b ρ j x else 0 :=
  projector_of_homogeneous b ρ i j _ (projector_homogeneous b ρ hcoassoc j x)

variable [Fintype ι]

/-- Finite tensor expansion in the specified basis. -/
theorem sum_coefficient (z : M ⊗[R] H) :
    ∑ i, coefficient b i z ⊗ₜ[R] b i = z := by
  induction z using TensorProduct.inductionOn with
  | tmul m h =>
    simp only [coefficient_tmul, TensorProduct.smul_tmul]
    rw [← TensorProduct.tmul_sum, b.sum_repr]
  | add z w hz hw => simp_all [TensorProduct.add_tmul, Finset.sum_add_distrib]

/-- The counit law makes the sum of projectors the identity. -/
theorem sum_projector (ρ : M →ₗ[R] M ⊗[R] H)
    (hcounit : ∀ x, TensorProduct.rid R M ((augmentation b).lTensor M (ρ x)) = x)
    (x : M) : ∑ i, projector b ρ i x = x := by
  have h := congrArg
    (fun z ↦ TensorProduct.rid R M ((augmentation b).lTensor M z))
    (sum_coefficient b (ρ x))
  simpa [projector, hcounit] using h

end CoactionBasis
