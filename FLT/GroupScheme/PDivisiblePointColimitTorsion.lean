/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisiblePointColimitGroup

/-! # Original finite-stage points remain p-primary torsion in the colimit -/

@[expose] public noncomputable section
open WithConv
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)
  {B : Type} [CommRing B] [Algebra R B]

/-- Generic torsion descends to equality of the original finite-flat multiplication maps. -/
theorem level_multiply_prime_pow (n : ℕ) :
    (X.level n).multiply (p ^ n) = (X.level n).multiply 0 := by
  apply genericHom_injective
  ext x
  simp only [FF.genericHom_multiply, X.killed, zero_smul]

/-- Every original level-n point is killed by p^n over every test algebra. -/
theorem pointColimitMk_pow_prime (n : ℕ) (x : (X.level n).CoordinateRing →ₐ[R] B) :
    X.pointColimitMk n x ^ (p ^ n) = 1 := by
  rw [← X.pointColimitMul_eq_pow, X.pointColimitMul_mk,
    X.level_multiply_prime_pow]
  change X.pointColimitMul 0 (X.pointColimitMk n x) = 1
  rw [X.pointColimitMul_eq_pow, pow_zero]

/-- The original point colimit consists of p-primary torsion points. -/
theorem pointColimit_exists_pow_prime_eq_one (x : X.PointColimit B) :
    ∃ n : ℕ, x ^ (p ^ n) = 1 := by
  induction x using DirectLimit.induction with
  | _ n x => exact ⟨n, X.pointColimitMk_pow_prime n x⟩

end ThreeAdicPlan.PDivisibleSystem
