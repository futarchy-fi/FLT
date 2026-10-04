/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCotangentFree
public import FLT.GroupScheme.PDivisibleIntegralTangent
public import FLT.Mathlib.LinearAlgebra.FreeDualReduction

/-! # The reduced integral dual is the original torsion-valued tangent functor -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

omit [IsDomain R] [IsLocalRing R] [Fact p.Prime] in
/-- The specified coefficient quotient is killed by the same natural-number power. -/
theorem cotangentCoefficient_pow_smul_eq_zero (n : ℕ)
    (a : R ⧸ Ideal.span {(p : R) ^ n}) : p ^ n • a = 0 := by
  rw [nsmul_eq_mul]
  have hz : (p ^ n : R ⧸ Ideal.span {(p : R) ^ n}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [Nat.cast_pow, hz, zero_mul]

/-- Reduction of the original integral tangent is all functionals on the original level. -/
def integralTangentReductionEquiv (e : R ≃+* ℤ_[p]) (n : ℕ) :
    (X.IntegralTangent ⧸ LinearMap.range
      ((p : R) ^ n • (LinearMap.id : X.IntegralTangent →ₗ[R] _))) ≃ₗ[R]
      (X.LevelCotangent n →ₗ[R] R ⧸ Ideal.span {(p : R) ^ n}) := by
  let : Module.Free R X.cotangentLimit := X.cotangentLimit_free e
  let (m : ℕ) : Finite (X.LevelCotangent m) := X.levelCotangent_finite_of_equiv e m
  exact (Module.dualReductionEquiv ((p : R) ^ n)).trans
    (X.cotangentTorsionEquiv n (cotangentCoefficient_pow_smul_eq_zero n)).symm

/-- Reduction preserves the original integral pairing at every limit vector. -/
theorem integralTangentReductionEquiv_pairing (e : R ≃+* ℤ_[p]) (n : ℕ)
    (f : X.IntegralTangent) (x : X.cotangentLimit) :
    X.integralTangentReductionEquiv e n (Submodule.Quotient.mk f) (X.cotangentEval n x) =
      Ideal.Quotient.mk _ (X.integralTangentPairing f x) := by
  let : Module.Free R X.cotangentLimit := X.cotangentLimit_free e
  let (m : ℕ) : Finite (X.LevelCotangent m) := X.levelCotangent_finite_of_equiv e m
  exact LinearMap.congr_fun ((X.cotangentTorsionEquiv n
    (cotangentCoefficient_pow_smul_eq_zero n)).apply_symm_apply
      (Module.dualReductionEquiv ((p : R) ^ n) (Submodule.Quotient.mk f))) x

/-- The same reduction represents the already constructed original Leibniz tangents. -/
def integralTangentTorsionEquiv (e : R ≃+* ℤ_[p]) (n : ℕ) :
    (X.IntegralTangent ⧸ LinearMap.range
      ((p : R) ^ n • (LinearMap.id : X.IntegralTangent →ₗ[R] _))) ≃ₗ[R]
      (X.level n).Tangent (M := R ⧸ Ideal.span {(p : R) ^ n}) :=
  (X.integralTangentReductionEquiv e n).trans (X.level n).cotangentTangentEquiv

end ThreeAdicPlan.PDivisibleSystem
