/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CoactionBasisProjectors

/-!
# Multiplication and coaction coefficients

A multiplicative basis allows one to extract the opposite degree from the
identity coefficient of a product with a homogeneous element.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace CoactionBasis

variable {R H S G : Type*} [CommRing R] [CommRing H] [Algebra R H]
  [CommRing S] [Algebra R S] [Group G] [Finite G]
  (b : Module.Basis G R H) (hmul : ∀ i j, b (i * j) = b i * b j)

omit [Group G] [Finite G] in
/-- Coefficients commute with multiplication from the left tensor factor. -/
theorem coefficient_left_mul (i : G) (a : S) (z : S ⊗[R] H) :
    coefficient b i ((a ⊗ₜ[R] (1 : H)) * z) = a * coefficient b i z := by
  induction z using TensorProduct.inductionOn with
  | tmul x h => simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def, mul_left_comm]
  | add z w hz hw => simp_all [mul_add]

include hmul in
/-- Multiplying by degree `i` shifts the identity coefficient to degree `i⁻¹`. -/
theorem coefficient_mul_degree (i : G) (a : S) (z : S ⊗[R] H) :
    coefficient b 1 (z * (a ⊗ₜ[R] b i)) = coefficient b i⁻¹ z * a := by
  classical
  let := Fintype.ofFinite G
  conv_lhs => rw [← sum_coefficient b z]
  simp only [Finset.sum_mul, map_sum, Algebra.TensorProduct.tmul_mul_tmul, ← hmul,
    coefficient_tmul, Module.Basis.repr_self, Finsupp.single_apply]
  simp only [mul_eq_one_iff_eq_inv, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

include hmul in
/-- Identity-degree projection of a product extracts the opposite component. -/
theorem projector_mul_homogeneous (ρ : S →ₐ[R] S ⊗[R] H) (i : G) (x y : S)
    (hy : ρ y = y ⊗ₜ[R] b i) :
    projector b ρ.toLinearMap 1 (x * y) = projector b ρ.toLinearMap i⁻¹ x * y := by
  change coefficient b 1 (ρ (x * y)) = _
  rw [map_mul, hy, coefficient_mul_degree b hmul]
  rfl

end CoactionBasis
