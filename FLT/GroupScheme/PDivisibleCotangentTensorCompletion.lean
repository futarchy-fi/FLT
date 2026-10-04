/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCotangentTensorReduction
public import FLT.GroupScheme.PDivisibleCartierDlogLimit

/-! # The integral cotangent tensor inverse limit is the completed coefficient tensor -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K S : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]
  [CommRing S] [Algebra R S] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height) [∀ n, Finite (X.LevelCotangent n)]

/-- The p-adic completion is taken integrally, before any inversion of p. -/
abbrev CompletedCotangentTensor :=
  AdicCompletion (Ideal.span {(p : R)}) (X.cotangentLimit ⊗[R] S)

/-- Levelwise quotient comparison identifies the actual limit with the completed tensor. -/
def cotangentTensorCompletionEquiv :
    X.CompletedCotangentTensor (S := S) ≃ₗ[R] X.CartierCotangentSequences (S := S) where
  toFun v := ⟨fun n ↦ X.cotangentTensorReductionEquiv n (v.val n), by
    intro m n h
    rw [← X.cotangentTensorReductionEquiv_transition h, v.property h]⟩
  invFun v := ⟨fun n ↦ (X.cotangentTensorReductionEquiv n).symm (v.val n), by
    intro m n h
    apply (X.cotangentTensorReductionEquiv m).injective
    rw [X.cotangentTensorReductionEquiv_transition, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
    exact v.property h⟩
  left_inv v := by
    apply Subtype.ext
    funext n
    exact LinearEquiv.symm_apply_apply _ _
  right_inv v := by
    apply Subtype.ext
    funext n
    exact LinearEquiv.apply_symm_apply _ _
  map_add' v w := by
    apply Subtype.ext
    funext n
    exact map_add _ _ _
  map_smul' r v := by
    apply Subtype.ext
    funext n
    exact (X.cotangentTensorReductionEquiv n).map_smul r (v.val n)

omit [IsDomain R] [IsPrincipalIdealRing R] in
/-- The completion comparison retains every original cotangent evaluation. -/
theorem cotangentTensorCompletionEquiv_of (v : X.cotangentLimit ⊗[R] S) (n : ℕ) :
    (X.cotangentTensorCompletionEquiv
      (AdicCompletion.of (Ideal.span {(p : R)}) _ v)).val n =
      (X.cotangentEval n).rTensor S v := rfl

omit [IsDomain R] [IsPrincipalIdealRing R] in
/-- Finite quotient coordinates determine an element of the completed coefficient tensor. -/
theorem completedCotangentTensor_ext {v w : X.CompletedCotangentTensor (S := S)}
    (h : ∀ n, (X.cotangentTensorCompletionEquiv v).val n =
      (X.cotangentTensorCompletionEquiv w).val n) : v = w :=
  X.cotangentTensorCompletionEquiv.injective (Subtype.ext (funext h))

/-- An actual dual Tate vector has an integral completed cotangent tensor. -/
def cartierTateCompletedDlog (q : integralClosure R (AlgebraicClosure K) →ₐ[R] S)
    (y : X.CartierTate) : X.CompletedCotangentTensor (S := S) :=
  X.cotangentTensorCompletionEquiv.symm (X.cartierTateDlog q y)

/-- Completion recovers precisely the original finite Cartier differential. -/
theorem cartierTateCompletedDlog_eval
    (q : integralClosure R (AlgebraicClosure K) →ₐ[R] S) (y : X.CartierTate) (n : ℕ) :
    (X.cotangentTensorCompletionEquiv (X.cartierTateCompletedDlog q y)).val n =
      X.cartierTateDlogAt q n y := by
  rw [cartierTateCompletedDlog, LinearEquiv.apply_symm_apply]
  rfl

/-- No choice of integral finite representatives changes the completed Cartier differential. -/
theorem cartierTateCompletedDlog_unique
    (q : integralClosure R (AlgebraicClosure K) →ₐ[R] S) (y : X.CartierTate)
    (v : X.CompletedCotangentTensor (S := S))
    (hv : ∀ n, (X.cotangentTensorCompletionEquiv v).val n = X.cartierTateDlogAt q n y) :
    v = X.cartierTateCompletedDlog q y := by
  apply X.completedCotangentTensor_ext
  intro n
  exact (hv n).trans (X.cartierTateCompletedDlog_eval q y n).symm

end ThreeAdicPlan.PDivisibleSystem
