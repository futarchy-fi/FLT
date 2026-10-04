/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceCompletedPointTopology
public import FLT.GroupScheme.PDivisiblePointColimitTorsion

/-! # Multiplication by powers of p contracts every original completed point -/

@[expose] public noncomputable section
open PadicHodgeTheory Filter
open scoped Topology
namespace ThreeAdicPlan.PDivisibleSystem
variable {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- At each fixed precision, sufficiently large p-powers are identically the identity. -/
theorem rationalPlaceCompletedPointEval_pow_eventually (x : X.RationalPlaceCompletedPoints)
    (s : ℕ) : ∀ᶠ n : ℕ in atTop, X.rationalPlaceCompletedPointEval s (x ^ (p ^ n)) = 1 := by
  obtain ⟨m, hm⟩ := X.pointColimit_exists_pow_prime_eq_one (X.rationalPlaceCompletedPointEval s x)
  filter_upwards [eventually_ge_atTop m] with n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [map_pow, pow_add p m k, pow_mul, hm, one_pow]

/-- Actual p-power iterates tend to the identity in the completed adic point group. -/
theorem rationalPlaceCompletedPoint_pow_tendsto (x : X.RationalPlaceCompletedPoints) :
    Tendsto (fun n : ℕ ↦ x ^ (p ^ n)) atTop (𝓝 1) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro s
  exact tendsto_nhds_of_eventually_eq (X.rationalPlaceCompletedPointEval_pow_eventually x s)

end ThreeAdicPlan.PDivisibleSystem
