/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.SemilinearFixedAlgebra

/-!
# Effective scalar recovery from Galois coordinates

An explicit Galois orthogonality relation on coefficient elements constructs
an inverse to scalar extension of the fixed algebra. The inputs concern only
the coefficient extension and the semilinear action; no scalar-recovery map
or isomorphism is assumed. Producing integral Galois coordinates for an
arithmetic splitting ring is a separate obligation.
-/

@[expose] public noncomputable section
open scoped BigOperators TensorProduct
namespace SemilinearDescent

universe u
variable {R S B : Type u} {G ι : Type*} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra S B] [Algebra R B] [IsScalarTower R S B]
  [Group G] [Fintype G] [DecidableEq G] [Fintype ι]
  (σ : G →* (S ≃ₐ[R] S)) (ρ : G →* (B ≃ₐ[R] B))
  (hρ : ∀ g s, ρ g (algebraMap S B s) = algebraMap S B (σ g s))
  (a b : ι → S)
  (hdual : ∀ g, ∑ i, a i * σ g (b i) = if g = 1 then 1 else 0)
  (tr : S →ₗ[R] R) (htr : ∀ s, algebraMap R S (tr s) = ∑ g, σ g s)

/-- The canonical multiplication map from scalar-extended fixed coordinates. -/
def recoveryMap : S ⊗[R] fixed ρ →ₐ[R] B :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S B) (fixed ρ).val
    (fun _ _ ↦ .all _ _)

/-- The inverse is the sum of Galois coordinates tensored with orbit sums. -/
def recoveryInverse : B →ₗ[R] S ⊗[R] fixed ρ where
  toFun x := ∑ i, a i ⊗ₜ[R] orbitSum ρ (algebraMap S B (b i) * x)
  map_add' x y := by simp [mul_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    simp [TensorProduct.tmul_smul, Finset.smul_sum]

include hdual htr in
/-- Galois orthogonality reconstructs every coefficient from its traces. -/
theorem coefficient_reconstruction (s : S) :
    ∑ i, a i * algebraMap R S (tr (b i * s)) = s := by
  simp only [htr, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, hdual]
  simp

omit [DecidableEq G] in
include hρ htr in
/-- The orbit sum of a coefficient times an invariant is its scalar trace. -/
theorem orbitSum_coefficient (s : S) (x : fixed ρ) :
    orbitSum ρ (algebraMap S B s * x) = tr s • x := by
  apply Subtype.ext
  rw [orbitSum_mul_fixed]
  simp only [hρ, ← map_sum, ← htr]
  rw [← IsScalarTower.algebraMap_apply R S B]
  exact (Algebra.smul_def (tr s) (x : B)).symm

include hρ hdual in
/-- The explicit inverse is a right inverse to multiplication. -/
theorem recoveryMap_inverse (x : B) :
    recoveryMap ρ (recoveryInverse ρ a b x) = x := by
  change recoveryMap ρ (∑ i, a i ⊗ₜ[R]
    orbitSum ρ (algebraMap S B (b i) * x)) = x
  simp only [map_sum]
  change (∑ i, algebraMap S B (a i) *
    ∑ g, ρ g (algebraMap S B (b i) * x)) = x
  simp only [map_mul, hρ, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← map_mul, ← Finset.sum_mul, ← map_sum, hdual]
  simp

include hρ hdual htr in
/-- The same formula is a left inverse on every tensor, not just fixed elements. -/
theorem recoveryInverse_map (z : S ⊗[R] fixed ρ) :
    recoveryInverse ρ a b (recoveryMap ρ z) = z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s x =>
    change (∑ i, a i ⊗ₜ[R]
      orbitSum ρ (algebraMap S B (b i) * (algebraMap S B s * x))) = s ⊗ₜ[R] x
    simp only [← mul_assoc, ← map_mul, orbitSum_coefficient σ ρ hρ tr htr]
    simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    simp only [Algebra.smul_def, mul_comm (algebraMap R S _)]
    rw [← TensorProduct.sum_tmul, coefficient_reconstruction σ a b hdual tr htr]

include hρ hdual htr in
/-- Scalar extension of the actual fixed algebra recovers the ambient algebra. -/
theorem recoveryMap_bijective : Function.Bijective (recoveryMap (S := S) ρ) :=
  ⟨Function.LeftInverse.injective (recoveryInverse_map σ ρ hρ a b hdual tr htr),
    Function.RightInverse.surjective (recoveryMap_inverse σ ρ hρ a b hdual)⟩

/-- The effective descent equivalence, constructed from coefficient orthogonality. -/
def recoveryEquiv : S ⊗[R] fixed ρ ≃ₐ[R] B :=
  AlgEquiv.ofBijective (recoveryMap ρ) (recoveryMap_bijective σ ρ hρ a b hdual tr htr)

end SemilinearDescent
