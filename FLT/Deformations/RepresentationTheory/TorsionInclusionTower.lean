/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.TorsionReductionTower

/-!
# Coherent inclusions of original torsion levels

The inclusion from level m to level n multiplies by a^(n-m). Composites
and both multiplication diagrams are proved on the original tensor modules.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace GaloisRepresentation.PrimePower
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Multiplication by a^(n-m) for any ordered pair of coefficient levels. -/
def coefficientEmbedding (a : R) {m n : ℕ} (h : m ≤ n) : Quot a m →ₗ[R] Quot a n :=
  (Ideal.span {a ^ m}).mapQ (Ideal.span {a ^ n}) (a ^ (n - m) • LinearMap.id) (by
    intro x hx
    change a ^ (n - m) * x ∈ Ideal.span {a ^ n}
    rw [Ideal.mem_span_singleton] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    refine ⟨y, ?_⟩
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel h])

/-- The original tensor inclusion between any two ordered levels. -/
def tensorEmbedding (a : R) {m n : ℕ} (h : m ≤ n) :
    Level (V := V) a m →ₗ[R] Level (V := V) a n :=
  (coefficientEmbedding a h).rTensor V

/-- These inclusions commute with every operator of the original representation. -/
theorem tensorEmbedding_natural (a : R) {m n : ℕ} (h : m ≤ n) (f : V →ₗ[R] V)
    (x : Level (V := V) a m) :
    tensorEmbedding a h (f.baseChange (Quot a m) x) =
      f.baseChange (Quot a n) (tensorEmbedding a h x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r v => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Two inclusions compose to the direct inclusion. -/
theorem tensorEmbedding_comp (a : R) {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) :
    (tensorEmbedding (V := V) a k).comp (tensorEmbedding a h) =
      tensorEmbedding a (h.trans k) := by
  apply TensorProduct.ext'
  intro r x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  change Ideal.Quotient.mk _ (a ^ (n - m) * (a ^ (m - l) * r)) ⊗ₜ[R] x =
    Ideal.Quotient.mk _ (a ^ (n - l) * r) ⊗ₜ[R] x
  rw [← mul_assoc, ← pow_add, show n - m + (m - l) = n - l by omega]

/-- Inclusion followed by reduction multiplies the lower level by a^(n-m). -/
theorem tensorTransition_embedding (a : R) {m n : ℕ} (h : m ≤ n) :
    (tensorTransition (V := V) a h).comp (tensorEmbedding a h) =
      a ^ (n - m) • LinearMap.id := by
  apply TensorProduct.ext'
  intro r x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  change Ideal.Quotient.mk _ (a ^ (n - m) * r) ⊗ₜ[R] x =
    a ^ (n - m) • (Ideal.Quotient.mk _ r ⊗ₜ[R] x)
  rw [TensorProduct.smul_tmul']
  rfl

/-- Reduction followed by inclusion multiplies the higher level by a^(n-m). -/
theorem tensorEmbedding_transition (a : R) {m n : ℕ} (h : m ≤ n) :
    (tensorEmbedding (V := V) a h).comp (tensorTransition a h) =
      a ^ (n - m) • LinearMap.id := by
  apply TensorProduct.ext'
  intro r x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  change Ideal.Quotient.mk _ (a ^ (n - m) * r) ⊗ₜ[R] x =
    a ^ (n - m) • (Ideal.Quotient.mk _ r ⊗ₜ[R] x)
  rw [TensorProduct.smul_tmul']
  rfl

/-- The exact-sequence inclusion is the corresponding inclusion in the tower. -/
theorem tensorEmbedding_eq_inclusion (a : R) (m n : ℕ) :
    tensorEmbedding (V := V) a (Nat.le_add_right m n) = tensorInclusion a m n := by
  apply TensorProduct.ext'
  intro r x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  change Ideal.Quotient.mk _ (a ^ (m + n - m) * r) ⊗ₜ[R] x =
    Ideal.Quotient.mk _ (a ^ n * r) ⊗ₜ[R] x
  rw [Nat.add_sub_cancel_left]

/-- Inclusion at the same tensor level is the identity. -/
@[simp] theorem tensorEmbedding_refl (a : R) (n : ℕ) :
    tensorEmbedding (V := V) a (le_refl n) = LinearMap.id := by
  apply TensorProduct.ext'
  intro r x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  change Ideal.Quotient.mk _ (a ^ (n - n) * r) ⊗ₜ[R] x = Ideal.Quotient.mk _ r ⊗ₜ[R] x
  rw [Nat.sub_self, pow_zero, one_mul]

end GaloisRepresentation.PrimePower
