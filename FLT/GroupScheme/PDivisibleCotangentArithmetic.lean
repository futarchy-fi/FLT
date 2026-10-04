/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlatCotangentArithmetic
public import FLT.GroupScheme.PDivisibleCotangentTransitions

/-! # Scalar differentials at the original p-power levels -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- Restriction after the original reduction pullback is the p-power scalar. -/
theorem cotangentRestriction_pullback_scalar {m n : ℕ} (h : m ≤ n) :
    (X.cotangentRestriction h).comp (X.cotangentPullback h) =
      p ^ (n - m) • LinearMap.id := by
  rw [X.cotangentRestriction_pullback, FF.cotangentMap_multiply]

/-- The opposite composite is the same scalar on the actual upper-level cotangent. -/
theorem cotangentPullback_restriction_scalar {m n : ℕ} (h : m ≤ n) :
    (X.cotangentPullback h).comp (X.cotangentRestriction h) =
      p ^ (n - m) • LinearMap.id := by
  rw [X.cotangentPullback_restriction, FF.cotangentMap_multiply]

/-- Every original level cotangent is annihilated by its specified p-power. -/
theorem cotangent_pow_smul_eq_zero (n : ℕ) (a : X.LevelCotangent n) : p ^ n • a = 0 :=
  (X.level n).cotangent_nsmul_eq_zero (p ^ n) (X.killed n) a

/-- The level-zero cotangent vanishes, as required by the original indexing. -/
theorem cotangent_zero_eq_zero (a : X.LevelCotangent 0) : a = 0 := by
  simpa only [pow_zero, one_nsmul] using X.cotangent_pow_smul_eq_zero 0 a

/-- Surjectivity of restriction identifies the pullback image with scalar multiples. -/
theorem cotangentPullback_range {m n : ℕ} (h : m ≤ n) :
    LinearMap.range (X.cotangentPullback h) =
      LinearMap.range (p ^ (n - m) • (LinearMap.id : X.LevelCotangent n →ₗ[R] _)) := by
  rw [← X.cotangentPullback_restriction_scalar h, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (X.cotangentRestriction_surjective h), Submodule.map_top]

end ThreeAdicPlan.PDivisibleSystem
