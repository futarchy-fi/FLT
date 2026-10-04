/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCotangentTensorCompletion
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # Coefficient specialization of the completed original Cartier differential -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K S T : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]
  [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height)
  [∀ n, Finite (X.LevelCotangent n)]

/-- Coefficient specialization is the standard adic completion of the original tensor map. -/
def completedCotangentCoefficients (f : S →ₐ[R] T) :
    X.CompletedCotangentTensor (S := S) →ₗ[R] X.CompletedCotangentTensor (S := T) :=
  (AdicCompletion.map (Ideal.span {(p : R)})
    (f.toLinearMap.lTensor X.cotangentLimit)).restrictScalars R

omit [IsDomain R] [IsPrincipalIdealRing R] [∀ n, Finite (X.LevelCotangent n)] in
/-- Specialization agrees with the original coefficient tensor map before completion. -/
theorem completedCotangentCoefficients_of (f : S →ₐ[R] T) (v : X.cotangentLimit ⊗[R] S) :
    X.completedCotangentCoefficients f (AdicCompletion.of (Ideal.span {(p : R)}) _ v) =
      AdicCompletion.of (Ideal.span {(p : R)}) _ (f.toLinearMap.lTensor _ v) :=
  AdicCompletion.map_of _ _ v

omit [IsDomain R] [IsPrincipalIdealRing R] in
/-- Completed coefficient specialization retains the actual finite-level tensors. -/
theorem completedCotangentCoefficients_eval (f : S →ₐ[R] T)
    (v : X.CompletedCotangentTensor (S := S)) (n : ℕ) :
    (X.cotangentTensorCompletionEquiv (X.completedCotangentCoefficients f v)).val n =
      f.toLinearMap.lTensor _ ((X.cotangentTensorCompletionEquiv v).val n) := by
  change X.cotangentTensorReductionEquiv n
    ((AdicCompletion.map _ (f.toLinearMap.lTensor X.cotangentLimit) v).val n) = _
  rw [AdicCompletion.map_val_apply]
  obtain ⟨w, hw⟩ := Submodule.mkQ_surjective _ (v.val n)
  change X.cotangentTensorReductionEquiv n
    ((f.toLinearMap.lTensor X.cotangentLimit).reduceModIdeal
      ((Ideal.span {(p : R)}) ^ n) (v.val n)) =
    f.toLinearMap.lTensor _ (X.cotangentTensorReductionEquiv n (v.val n))
  rw [← hw]
  change (X.cotangentEval n).rTensor T (f.toLinearMap.lTensor _ w) =
    f.toLinearMap.lTensor _ ((X.cotangentEval n).rTensor S w)
  clear hw
  induction w using TensorProduct.inductionOn with
  | tmul x s => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The actual completed dual Tate differential is natural for every integral coefficient map. -/
theorem cartierTateCompletedDlog_coefficients
    (q : integralClosure R (AlgebraicClosure K) →ₐ[R] S) (f : S →ₐ[R] T)
    (y : X.CartierTate) :
    X.completedCotangentCoefficients f (X.cartierTateCompletedDlog q y) =
      X.cartierTateCompletedDlog (f.comp q) y := by
  apply X.completedCotangentTensor_ext
  intro n
  rw [X.completedCotangentCoefficients_eval, X.cartierTateCompletedDlog_eval,
    X.cartierTateCompletedDlog_eval, X.cartierTateDlogAt_coefficients]

end ThreeAdicPlan.PDivisibleSystem
