/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.RingTheory.Coalgebra.Convolution

/-!
# Convolution of rank-one linear maps

A rank-one map sends an input to a functional value times a fixed vector.
Convolution multiplies the vectors and convolves the functionals. This
includes the zeroth power, where the functional is the counit.
-/

@[expose] public noncomputable section
open WithConv
namespace ThreeAdicPlan

variable {R A C : Type*} [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup C] [Module R C] [Coalgebra R C]

/-- Convolution of rank-one maps multiplies their two factors separately. -/
theorem rankOne_convMul (φ ψ : WithConv (C →ₗ[R] R)) (x y : A) :
    toConv (φ.ofConv.smulRight x) * toConv (ψ.ofConv.smulRight y) =
      toConv ((φ * ψ).ofConv.smulRight (x * y)) := by
  ext c
  rw [(Coalgebra.Repr.arbitrary R c).convMul_apply]
  change _ = (φ * ψ) c • (x * y)
  rw [(Coalgebra.Repr.arbitrary R c).convMul_apply]
  simp only [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [LinearMap.smulRight_apply]
  exact smul_mul_smul_comm _ _ _ _

/-- Every convolution power is the corresponding rank-one power map. -/
theorem rankOne_convPow (φ : WithConv (C →ₗ[R] R)) (x : A) (n : ℕ) :
    toConv (φ.ofConv.smulRight x) ^ n =
      toConv ((φ ^ n).ofConv.smulRight (x ^ n)) := by
  induction n with
  | zero =>
    ext c
    simp [Algebra.algebraMap_eq_smul_one]
  | succ n hn => rw [pow_succ, hn, rankOne_convMul, ← pow_succ, ← pow_succ]

/-- Evaluation of a convolution power is the powered functional times the powered vector. -/
theorem rankOne_convPow_apply (φ : WithConv (C →ₗ[R] R)) (x : A) (n : ℕ) (c : C) :
    (toConv (φ.ofConv.smulRight x) ^ n) c = (φ ^ n) c • x ^ n := by
  rw [rankOne_convPow]
  rfl

end ThreeAdicPlan
