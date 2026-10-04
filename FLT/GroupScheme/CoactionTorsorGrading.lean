/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CoactionBasisMultiplication
public import Mathlib.Algebra.Algebra.Operations

/-!
# Opposite components of a diagonal torsor

Project the inverse image of a universal degree element under the torsor
comparison. Multiplication of the two projected factors gives one.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace CoactionBasis

variable {R S H G : Type*} [CommRing R] [CommRing S] [CommRing H]
  [Algebra R S] [Algebra R H] [Group G] [Finite G]
  (b : Module.Basis G R H) (hone : b 1 = 1)
  (hmul : ∀ i j, b (i * j) = b i * b j) (ρ : S →ₐ[R] S ⊗[R] H)
  (C : G → Submodule R S) (hC : ∀ i x, x ∈ C i ↔ ρ x = x ⊗ₜ[R] b i)
  (hcoassoc : ∀ x, TensorProduct.assoc R S H H (ρ.toLinearMap.rTensor H (ρ x)) =
    (diagonal b).lTensor S (ρ x))

omit [Group G] [Finite G] in
include hC hcoassoc in
/-- The two projected tensor factors multiply into their homogeneous product. -/
theorem projected_mul_mem (i j : G) (z : S ⊗[R] S) :
    (LinearMap.mul' R S)
      (TensorProduct.map (projector b ρ.toLinearMap i) (projector b ρ.toLinearMap j) z) ∈
      C i * C j := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [TensorProduct.map_tmul, LinearMap.mul'_apply]
    exact Submodule.mul_mem_mul
      ((hC i _).mpr (projector_homogeneous b ρ.toLinearMap hcoassoc i x))
      ((hC j _).mpr (projector_homogeneous b ρ.toLinearMap hcoassoc j y))
  | add z w hz hw => simpa only [map_add] using Submodule.add_mem _ hz hw

include hone hmul hC hcoassoc in
/-- A torsor comparison yields strong grading, without a supplied generator. -/
theorem one_mem_opposite_product (T : S ⊗[R] S ≃ₐ[S] S ⊗[R] H)
    (hT : ∀ y, T (1 ⊗ₜ[R] y) = ρ y) (i : G) : (1 : S) ∈ C i⁻¹ * C i := by
  classical
  have he : ∀ z : S ⊗[R] S,
      (LinearMap.mul' R S)
        (TensorProduct.map (projector b ρ.toLinearMap i⁻¹) (projector b ρ.toLinearMap i) z) =
        projector b ρ.toLinearMap 1 (coefficient b i (T z)) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      simp only [TensorProduct.map_tmul, LinearMap.mul'_apply]
      have ht : T (x ⊗ₜ[R] y) = (x ⊗ₜ[R] (1 : H)) * ρ y := by
        have hxy : x ⊗ₜ[R] y = (x ⊗ₜ[R] (1 : S)) * (1 ⊗ₜ[R] y) := by
          simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [hxy, map_mul, hT]
        exact congrArg (· * ρ y) (T.commutes x)
      rw [ht, coefficient_left_mul]
      exact (projector_mul_homogeneous b hmul ρ i x (projector b ρ.toLinearMap i y)
        (projector_homogeneous b ρ.toLinearMap hcoassoc i y)).symm
    | add z w hz hw => simp only [map_add, hz, hw]
  have hmem := projected_mul_mem b ρ C hC hcoassoc i⁻¹ i (T.symm (1 ⊗ₜ[R] b i))
  rw [he, T.apply_symm_apply, coefficient_tmul] at hmem
  have hp : projector b ρ.toLinearMap 1 (1 : S) = 1 := by
    apply (projector_of_homogeneous b ρ.toLinearMap 1 1 1 ?_).trans (ite_eq_left rfl)
    simp [hone, Algebra.TensorProduct.one_def]
  simpa only [Module.Basis.repr_self, Finsupp.single_eq_same, one_smul, hp] using hmem

end CoactionBasis
