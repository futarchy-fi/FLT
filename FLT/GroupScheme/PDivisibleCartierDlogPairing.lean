/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCartierDlogLimit
public import FLT.GroupScheme.PDivisibleCartierDifferential

/-! # Original dual Tate characters and the original integral tangent pairing -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan.PDivisibleSystem
open HopfAlgebra.CartierDual
variable {R K S : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]
  [CommRing S] [Algebra R S] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- A Tate character's finite differential is the original integral tangent coefficient pairing. -/
theorem cartierTateDlogAt_integralPairing (e : R ≃+* ℤ_[p])
    (q : integralClosure R (AlgebraicClosure K) →ₐ[R] S) (n : ℕ)
    (hS : ∀ a : S, p ^ n • a = 0) (y : X.CartierTate)
    (z : X.IntegralTangent ⊗[R] S) (v : X.cotangentLimit ⊗[R] S)
    (hv : (X.cotangentEval n).rTensor S v = X.cartierTateDlogAt q n y) :
    X.integralCotangentCoefficientPairing e z v =
      testLogDifferential (q.comp (X.cartierTateIntegralCoordinate n y))
        ((X.level n).cotangentTangentEquiv
          (X.integralTangentLevelCoefficientsEquiv e n hS z)) :=
  X.cartierDifferential_of_representative e n hS _ z v hv

/-- At every level the actual Tate tensor has an original cotangent-limit representative. -/
theorem cartierTateDlogAt_representative_exists
    (q : integralClosure R (AlgebraicClosure K) →ₐ[R] S) (n : ℕ) (y : X.CartierTate) :
    ∃ v : X.cotangentLimit ⊗[R] S,
      (X.cotangentEval n).rTensor S v = X.cartierTateDlogAt q n y :=
  X.cartierDlog_representative_exists n _

/-- The actual extended Tate character agrees with dlog on every square-zero integral test point. -/
theorem cartierTateCharacter_squareZero
    (q : integralClosure R (AlgebraicClosure K) →ₐ[R] S) (n : ℕ) (y : X.CartierTate)
    {T : Type} [CommRing T] [Algebra R T] (r : S →ₐ[R] T)
    (hJ : RingHom.ker r ^ 2 = ⊥)
    (f : (Bialgebra.counitAlgHom R (X.level n).CoordinateRing).AugmentationPointKernel r) :
    ((X.level n).integralCartierCharacter (X.cartierTateEval n y) q
      (WithConv.toConv f.val) : S) - 1 =
        testLogDifferential (q.comp (X.cartierTateIntegralCoordinate n y))
          (testKernelTangent r hJ f) :=
  testCharacter_squareZero _ r hJ f

end ThreeAdicPlan.PDivisibleSystem
