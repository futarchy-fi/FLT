/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCotangentTensorCompletion
public import FLT.GroupScheme.CartierDlogAdditivity
public import FLT.GroupScheme.RaynaudIntegralPointAddition

/-! # Additivity of actual finite, inverse-limit and completed Tate differentials -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan.PDivisibleSystem
open HopfAlgebra.CartierDual
variable {R K S : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]
  [CommRing S] [Algebra R S] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

local instance dlogCoordinateFree (n : ℕ) : Module.Free R (X.level n).CoordinateRing :=
  Module.free_of_flat_of_isLocalRing

/-- The actual finite Tate dlog is additive on the original dual Tate module. -/
theorem cartierTateDlogAt_add (q : integralClosure R (AlgebraicClosure K) →ₐ[R] S)
    (n : ℕ) (y z : X.CartierTate) :
    X.cartierTateDlogAt q n (y + z) = X.cartierTateDlogAt q n y + X.cartierTateDlogAt q n z := by
  unfold cartierTateDlogAt cartierTateIntegralCoordinate FF.cartierDlog
  rw [map_add]
  erw [FF.integralPointCoordinate_add, AlgHom.comp_convMul_distrib, testDlog_mul]

/-- The zero dual Tate vector has zero differential at every original level. -/
@[simp] theorem cartierTateDlogAt_zero (q : integralClosure R (AlgebraicClosure K) →ₐ[R] S)
    (n : ℕ) : X.cartierTateDlogAt q n 0 = 0 := by
  unfold cartierTateDlogAt cartierTateIntegralCoordinate FF.cartierDlog
  rw [map_zero]
  erw [FF.integralPointCoordinate_zero]
  have h : q.comp (1 : WithConv (HopfAlgebra.CartierDual R
      (X.level n).CoordinateRing →ₐ[R] integralClosure R (AlgebraicClosure K))).ofConv =
      (1 : WithConv (HopfAlgebra.CartierDual R (X.level n).CoordinateRing →ₐ[R] S)).ofConv := by
    ext a
    simp
  change testDlog (q.comp (1 : WithConv (HopfAlgebra.CartierDual R
    (X.level n).CoordinateRing →ₐ[R] integralClosure R (AlgebraicClosure K))).ofConv) = 0
  rw [h]
  exact testDlog_one

/-- The original finite differential as an additive map. -/
def cartierTateDlogAtHom (q : integralClosure R (AlgebraicClosure K) →ₐ[R] S) (n : ℕ) :
    X.CartierTate →+ X.LevelCotangent n ⊗[R] S where
  toFun := X.cartierTateDlogAt q n
  map_zero' := X.cartierTateDlogAt_zero q n
  map_add' := X.cartierTateDlogAt_add q n

/-- The coherent integral tensor construction is an additive map, without a linearity assumption. -/
def cartierTateDlogHom (q : integralClosure R (AlgebraicClosure K) →ₐ[R] S) :
    X.CartierTate →+ X.CartierCotangentSequences (S := S) where
  toFun := X.cartierTateDlog q
  map_zero' := by
    apply Subtype.ext
    funext n
    exact X.cartierTateDlogAt_zero q n
  map_add' y z := by
    apply Subtype.ext
    funext n
    exact X.cartierTateDlogAt_add q n y z

variable [∀ n, Finite (X.LevelCotangent n)]

/-- The actual Tate dlog is additive in the completed integral coefficient tensor. -/
def cartierTateCompletedDlogHom (q : integralClosure R (AlgebraicClosure K) →ₐ[R] S) :
    X.CartierTate →+ X.CompletedCotangentTensor (S := S) :=
  X.cotangentTensorCompletionEquiv.symm.toLinearMap.toAddMonoidHom.comp (X.cartierTateDlogHom q)

/-- This homomorphism is the original completed differential, with no replacement coordinates. -/
theorem cartierTateCompletedDlogHom_apply
    (q : integralClosure R (AlgebraicClosure K) →ₐ[R] S) (y : X.CartierTate) :
    X.cartierTateCompletedDlogHom q y = X.cartierTateCompletedDlog q y := rfl

end ThreeAdicPlan.PDivisibleSystem
