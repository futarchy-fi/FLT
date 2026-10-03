/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.TorsionTensorMaps

/-!
# All transition maps of the original reduction tower

Reduction for any ordered pair of levels is coherent under composition.
These maps act on the original quotient tensor modules.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace GaloisRepresentation.PrimePower
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Coefficient reduction for an arbitrary inequality of levels. -/
def coefficientTransition (a : R) {m n : ℕ} (h : m ≤ n) : Quot a n →ₗ[R] Quot a m :=
  (Ideal.span {a ^ n}).mapQ (Ideal.span {a ^ m}) LinearMap.id (by
    intro x hx
    change x ∈ Ideal.span {a ^ m}
    rw [Ideal.mem_span_singleton] at hx ⊢
    exact (pow_dvd_pow a h).trans hx)

/-- Reduction between any two original tensor levels. -/
def tensorTransition (a : R) {m n : ℕ} (h : m ≤ n) :
    Level (V := V) a n →ₗ[R] Level (V := V) a m :=
  (coefficientTransition a h).rTensor V

/-- All reduction transitions commute with the original linear operators. -/
theorem tensorTransition_natural (a : R) {m n : ℕ} (h : m ≤ n) (f : V →ₗ[R] V)
    (x : Level (V := V) a n) :
    tensorTransition a h (f.baseChange (Quot a n) x) =
      f.baseChange (Quot a m) (tensorTransition a h x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r v => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Reducing twice agrees with the direct reduction. -/
theorem tensorTransition_comp (a : R) {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) :
    (tensorTransition (V := V) a h).comp (tensorTransition a k) =
      tensorTransition a (h.trans k) := by
  apply TensorProduct.ext'
  intro r x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  rfl

/-- Reduction at the same level is the identity. -/
@[simp] theorem tensorTransition_refl (a : R) (n : ℕ) :
    tensorTransition (V := V) a (le_refl n) = LinearMap.id := by
  apply TensorProduct.ext'
  intro r x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  rfl

/-- The exact-sequence reduction is the corresponding tower transition. -/
theorem tensorTransition_eq_reduction (a : R) (m n : ℕ) :
    tensorTransition (V := V) a (Nat.le_add_left n m) = tensorReduction a m n := by
  apply TensorProduct.ext'
  intro r x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  rfl

end GaloisRepresentation.PrimePower
