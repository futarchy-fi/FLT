/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleIntegralTangentReduction
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # The original integral cotangent and tangent form a perfect pairing -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- Evaluation identifies the original cotangent with the full dual of the integral tangent. -/
def cotangentIntegralBidualEquiv (e : R ≃+* ℤ_[p]) :
    X.cotangentLimit ≃ₗ[R] Module.Dual R X.IntegralTangent := by
  let : Module.Free R X.cotangentLimit := X.cotangentLimit_free e
  let : Module.Finite R X.cotangentLimit := X.cotangentLimit_finite e
  exact Module.evalEquiv R X.cotangentLimit

/-- This bidual equivalence is the original evaluation, without a chosen basis in its formula. -/
theorem cotangentIntegralBidualEquiv_apply (e : R ≃+* ℤ_[p])
    (x : X.cotangentLimit) (d : X.IntegralTangent) :
    X.cotangentIntegralBidualEquiv e x d = X.integralTangentPairing d x := rfl

/-- The integral pairing detects every original cotangent vector. -/
theorem cotangent_eq_zero_of_integral_pairings (e : R ≃+* ℤ_[p]) (x : X.cotangentLimit)
    (hx : ∀ d : X.IntegralTangent, X.integralTangentPairing d x = 0) : x = 0 := by
  apply (X.cotangentIntegralBidualEquiv e).injective
  rw [map_zero]
  ext d
  exact hx d

end ThreeAdicPlan.PDivisibleSystem
