/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleIntegralTangentReduction
public import Mathlib.LinearAlgebra.Contraction

/-! # Arbitrary coefficient modules in the original integral tangent pairing -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K M : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  [AddCommGroup M] [Module R M] (X : PDivisibleSystem R K p height)

/-- Extending coefficients in the integral tangent gives every module-valued functional. -/
def integralTangentCoefficientsEquiv (e : R ≃+* ℤ_[p]) :
    X.IntegralTangent ⊗[R] M ≃ₗ[R] (X.cotangentLimit →ₗ[R] M) := by
  let : Module.Free R X.cotangentLimit := X.cotangentLimit_free e
  let : Module.Finite R X.cotangentLimit := X.cotangentLimit_finite e
  exact dualTensorHomEquiv R X.cotangentLimit M

/-- Coefficient extension preserves the integral evaluation pairing on pure tensors. -/
theorem integralTangentCoefficientsEquiv_tmul (e : R ≃+* ℤ_[p])
    (d : X.IntegralTangent) (a : M) (x : X.cotangentLimit) :
    X.integralTangentCoefficientsEquiv e (d ⊗ₜ a) x = X.integralTangentPairing d x • a := rfl

/-- For p-power torsion coefficients this is precisely the already represented original level. -/
def integralTangentLevelCoefficientsEquiv (e : R ≃+* ℤ_[p])
    (n : ℕ) (hM : ∀ a : M, p ^ n • a = 0) :
    X.IntegralTangent ⊗[R] M ≃ₗ[R] (X.LevelCotangent n →ₗ[R] M) := by
  let (m : ℕ) : Finite (X.LevelCotangent m) := X.levelCotangent_finite_of_equiv e m
  exact (X.integralTangentCoefficientsEquiv e).trans (X.cotangentTorsionEquiv n hM).symm

/-- At each original level the scalar-extended pairing agrees with evaluation on the limit. -/
theorem integralTangentLevelCoefficientsEquiv_pairing (e : R ≃+* ℤ_[p])
    (n : ℕ) (hM : ∀ a : M, p ^ n • a = 0)
    (d : X.IntegralTangent) (a : M) (x : X.cotangentLimit) :
    X.integralTangentLevelCoefficientsEquiv e n hM (d ⊗ₜ a) (X.cotangentEval n x) =
      X.integralTangentPairing d x • a := by
  let (m : ℕ) : Finite (X.LevelCotangent m) := X.levelCotangent_finite_of_equiv e m
  exact LinearMap.congr_fun ((X.cotangentTorsionEquiv n hM).apply_symm_apply
    (X.integralTangentCoefficientsEquiv e (d ⊗ₜ a))) x

end ThreeAdicPlan.PDivisibleSystem
