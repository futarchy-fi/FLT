/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCotangentComplete
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Integral coefficient reduction of the original cotangent limit -/

@[expose] public noncomputable section
open scoped TensorProduct Pointwise
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K S : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [CommRing S] [Algebra R S]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height)
  [∀ n, Finite (X.LevelCotangent n)]

/-- Tensoring the original evaluation retains exactly its p-power kernel, without flatness. -/
theorem cotangentTensorEval_ker (n : ℕ) :
    LinearMap.ker ((X.cotangentEval n).rTensor S) =
      (Ideal.span {(p : R)}) ^ n • (⊤ : Submodule R (X.cotangentLimit ⊗[R] S)) := by
  have hex : Function.Exact
      (p ^ n • (LinearMap.id : X.cotangentLimit →ₗ[R] _)) (X.cotangentEval n) :=
    LinearMap.exact_iff.mpr (X.cotangentEval_ker n)
  rw [(rTensor_exact S hex (X.cotangentEval_surjective n)).linearMap_ker_eq]
  have ht : (p ^ n • (LinearMap.id : X.cotangentLimit →ₗ[R] _)).rTensor S =
      p ^ n • (LinearMap.id : (X.cotangentLimit ⊗[R] S) →ₗ[R] _) := by
    ext x s
    change (p ^ n • x) ⊗ₜ[R] s = p ^ n • (x ⊗ₜ[R] s)
    simp only [TensorProduct.smul_tmul']
  rw [ht]
  ext x
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rfl

/-- Actual finite cotangent tensors are the p-adic quotients of the integral coefficient tensor. -/
def cotangentTensorReductionEquiv (n : ℕ) :
    ((X.cotangentLimit ⊗[R] S) ⧸
      ((Ideal.span {(p : R)}) ^ n • (⊤ : Submodule R (X.cotangentLimit ⊗[R] S)))) ≃ₗ[R]
      X.LevelCotangent n ⊗[R] S :=
  (Submodule.quotEquivOfEq _ _ (X.cotangentTensorEval_ker (S := S) n).symm).trans
    (((X.cotangentEval n).rTensor S).quotKerEquivOfSurjective
      (LinearMap.rTensor_surjective S (X.cotangentEval_surjective n)))

/-- The quotient identification uses the original evaluation on every representative. -/
theorem cotangentTensorReductionEquiv_mk (n : ℕ) (v : X.cotangentLimit ⊗[R] S) :
    X.cotangentTensorReductionEquiv n (Submodule.Quotient.mk v) =
      (X.cotangentEval n).rTensor S v := rfl

omit [∀ n, Finite (X.LevelCotangent n)] in
/-- Coefficient extension preserves the original restriction identity. -/
theorem cotangentTensorEval_restriction {m n : ℕ} (h : m ≤ n)
    (v : X.cotangentLimit ⊗[R] S) :
    (X.cotangentRestriction h).rTensor S ((X.cotangentEval n).rTensor S v) =
      (X.cotangentEval m).rTensor S v := by
  induction v using TensorProduct.inductionOn with
  | tmul x s => simp only [LinearMap.rTensor_tmul, X.cotangentEval_restriction]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Quotient transitions are precisely the original restrictions after coefficient extension. -/
theorem cotangentTensorReductionEquiv_transition {m n : ℕ} (h : m ≤ n)
    (v : (X.cotangentLimit ⊗[R] S) ⧸
      ((Ideal.span {(p : R)}) ^ n • (⊤ : Submodule R (X.cotangentLimit ⊗[R] S)))) :
    X.cotangentTensorReductionEquiv m
        (AdicCompletion.transitionMap (Ideal.span {(p : R)}) _ h v) =
      (X.cotangentRestriction h).rTensor S (X.cotangentTensorReductionEquiv n v) := by
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ v
  exact (X.cotangentTensorEval_restriction h v).symm

end ThreeAdicPlan.PDivisibleSystem
