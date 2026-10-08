/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.DirectSum.Module

/-!
# Finite products and direct sums of original modules

Exchange a finite coordinate product with a direct sum by the original
coordinate evaluation maps. Finiteness is used only for the inverse's sum
of coordinate inclusions; the comparison itself is canonical.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open scoped DirectSum

universe r u v w

namespace FLT.Mazur.FiniteProductDirectSum

variable (R : Type r) [CommRing R] {κ : Type v} {ι : Type w}
  (M : κ → ι → Type u) [∀ n i, AddCommGroup (M n i)] [∀ n i, Module R (M n i)]

/-- Evaluate each original direct-sum coefficient at each product coordinate. -/
def evaluate : (⨁ n, ∀ i, M n i) →ₗ[R] ∀ i, ⨁ n, M n i :=
  LinearMap.pi fun i ↦ DirectSum.lmap fun n ↦ LinearMap.proj (φ := M n) i

/-- Evaluation is the original coefficient function with its two indices exchanged. -/
lemma evaluate_apply (x : ⨁ n, ∀ i, M n i) (i : ι) (n : κ) :
    evaluate R M x i n = x n i := rfl

variable [Fintype ι]

/-- Finite addition of coordinate inclusions reconstructs an original direct-sum element. -/
def assemble : (∀ i, ⨁ n, M n i) →ₗ[R] ⨁ n, ∀ i, M n i := by
  classical
  exact ∑ i, (DirectSum.lmap fun n ↦ LinearMap.single R (M n) i).comp (LinearMap.proj i)

/-- Reconstruction is the finite sum of the original single-coordinate functions. -/
lemma assemble_apply (x : ∀ i, ⨁ n, M n i) (n : κ) :
    assemble R M x n = fun i ↦ x i n := by
  classical
  ext i
  simp [assemble]

/-- The finite-product exchange retains exactly the original coefficient functions. -/
def equiv : (⨁ n, ∀ i, M n i) ≃ₗ[R] ∀ i, ⨁ n, M n i where
  toLinearMap := evaluate R M
  invFun := assemble R M
  left_inv x := by
    apply DFinsupp.ext
    intro n
    rw [assemble_apply]
    rfl
  right_inv x := by
    funext i
    apply DFinsupp.ext
    intro n
    change evaluate R M (assemble R M x) i n = x i n
    rw [evaluate_apply, assemble_apply]

/-- The inverse exchange also retains every original coefficient. -/
lemma equiv_symm_apply (x : ∀ i, ⨁ n, M n i) (n : κ) (i : ι) :
    (equiv R M).symm x n i = x i n := congrFun (assemble_apply R M x n) i

end FLT.Mazur.FiniteProductDirectSum
