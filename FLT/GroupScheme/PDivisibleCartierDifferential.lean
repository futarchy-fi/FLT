/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlatCartierDifferential
public import FLT.GroupScheme.PDivisibleIntegralTangentCoefficients

/-! # Cartier logarithmic derivatives use the original integral tangent coefficient pairing -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan.PDivisibleSystem
open HopfAlgebra.CartierDual
variable {R K S : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [CommRing S] [Algebra R S]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height)
local instance coefficientCoordinateFree (n : ℕ) : Module.Free R (X.level n).CoordinateRing :=
  Module.free_of_flat_of_isLocalRing

/-- Contract a scalar-extended cotangent with the existing original integral tangent pairing. -/
def integralCotangentCoefficientPairing (e : R ≃+* ℤ_[p])
    (z : X.IntegralTangent ⊗[R] S) (v : X.cotangentLimit ⊗[R] S) : S :=
  LinearMap.mul' R S ((X.integralTangentCoefficientsEquiv e z).rTensor S v)

/-- Pure tensors retain the already proved original integral evaluation, with both coefficients. -/
theorem integralCotangentCoefficientPairing_tmul (e : R ≃+* ℤ_[p])
    (d : X.IntegralTangent) (a b : S) (v : X.cotangentLimit) :
    X.integralCotangentCoefficientPairing e (d ⊗ₜ a) (v ⊗ₜ b) =
      (X.integralTangentPairing d v • a) * b := rfl

/-- Any representative of the finite character's cotangent tensor gives its actual differential. -/
theorem cartierDifferential_of_representative (e : R ≃+* ℤ_[p]) (n : ℕ)
    (hS : ∀ a : S, p ^ n • a = 0)
    (ψ : HopfAlgebra.CartierDual R (X.level n).CoordinateRing →ₐ[R] S)
    (z : X.IntegralTangent ⊗[R] S) (v : X.cotangentLimit ⊗[R] S)
    (hv : (X.cotangentEval n).rTensor S v = (X.level n).cartierDlog ψ) :
    X.integralCotangentCoefficientPairing e z v =
      testLogDifferential ψ ((X.level n).cotangentTangentEquiv
        (X.integralTangentLevelCoefficientsEquiv e n hS z)) := by
  rw [← FF.cartierDlog_pairing, ← hv]
  unfold integralCotangentCoefficientPairing
  congr 1
  clear hv
  induction v using TensorProduct.inductionOn with
  | tmul v s =>
    simp only [LinearMap.rTensor_tmul]
    congr 1
    let (m : ℕ) : Finite (X.LevelCotangent m) := X.levelCotangent_finite_of_equiv e m
    exact (LinearMap.congr_fun ((X.cotangentTorsionEquiv n hS).apply_symm_apply
      (X.integralTangentCoefficientsEquiv e z)) v).symm
  | add v w hv hw => simp only [map_add, hv, hw]

omit [IsDomain R] in
/-- The representative exists by surjectivity of the original cotangent evaluation. -/
theorem cartierDlog_representative_exists (n : ℕ)
    (ψ : HopfAlgebra.CartierDual R (X.level n).CoordinateRing →ₐ[R] S) :
    ∃ v : X.cotangentLimit ⊗[R] S,
      (X.cotangentEval n).rTensor S v = (X.level n).cartierDlog ψ :=
  LinearMap.rTensor_surjective S (X.cotangentEval_surjective n) _

/-- The integral contraction is independent of the chosen lift of this finite dlog tensor. -/
theorem cartierDifferential_representative_independent (e : R ≃+* ℤ_[p]) (n : ℕ)
    (hS : ∀ a : S, p ^ n • a = 0)
    (ψ : HopfAlgebra.CartierDual R (X.level n).CoordinateRing →ₐ[R] S)
    (z : X.IntegralTangent ⊗[R] S) (v w : X.cotangentLimit ⊗[R] S)
    (hv : (X.cotangentEval n).rTensor S v = (X.level n).cartierDlog ψ)
    (hw : (X.cotangentEval n).rTensor S w = (X.level n).cartierDlog ψ) :
    X.integralCotangentCoefficientPairing e z v =
      X.integralCotangentCoefficientPairing e z w :=
  (X.cartierDifferential_of_representative e n hS ψ z v hv).trans
    (X.cartierDifferential_of_representative e n hS ψ z w hw).symm

end ThreeAdicPlan.PDivisibleSystem
