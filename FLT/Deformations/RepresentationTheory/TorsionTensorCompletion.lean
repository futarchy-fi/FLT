/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.TorsionReductionTower
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.AdicCompletion.Basic

/-! # Comparing the actual tensor levels with adic-completion quotients -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace GaloisRepresentation.PrimePower
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The actual tensor level is the quotient by the corresponding power submodule. -/
def tensorCompletionLevel (a : R) (n : ℕ) :
    Level (V := V) a n ≃ₗ[R] V ⧸ ((Ideal.span {a}) ^ n • ⊤ : Submodule R V) :=
  (TensorProduct.quotTensorEquivQuotSMul V (Ideal.span {a ^ n})).trans
    (Submodule.quotEquivOfEq _ _ (by rw [Ideal.span_singleton_pow]))

/-- A vector maps to its own residue class under the level comparison. -/
theorem tensorCompletionLevel_one_tmul (a : R) (n : ℕ) (v : V) :
    tensorCompletionLevel a n (1 ⊗ₜ[R] v) = Submodule.Quotient.mk v := by
  simp [tensorCompletionLevel, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]

/-- Every tensor residue comes from a vector in the original lattice. -/
theorem one_tmul_surjective (a : R) (n : ℕ) :
    Function.Surjective (fun v : V ↦ (1 : Quot a n) ⊗ₜ[R] v) := by
  intro x
  obtain ⟨v, hv⟩ := Submodule.mkQ_surjective
    ((Ideal.span {a}) ^ n • (⊤ : Submodule R V)) (tensorCompletionLevel a n x)
  refine ⟨v, (tensorCompletionLevel a n).injective ?_⟩
  rw [tensorCompletionLevel_one_tmul]
  exact hv

/-- The original reduction maps become the actual completion transition maps. -/
theorem tensorCompletionLevel_transition (a : R) {m n : ℕ} (h : m ≤ n)
    (x : Level (V := V) a n) :
    tensorCompletionLevel a m (tensorTransition a h x) =
      AdicCompletion.transitionMap (Ideal.span {a}) V h (tensorCompletionLevel a n x) := by
  obtain ⟨v, rfl⟩ := one_tmul_surjective a n x
  change tensorCompletionLevel a m (1 ⊗ₜ[R] v) = _
  rw [tensorCompletionLevel_one_tmul, tensorCompletionLevel_one_tmul]
  rfl

end GaloisRepresentation.PrimePower
