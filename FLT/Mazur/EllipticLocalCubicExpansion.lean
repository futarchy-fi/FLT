/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalQuadratic
public import FLT.Mazur.EllipticLocalMultiplication

/-!
# Cubic remainder and residue divisibility on actual E₁ points

The multiplication series has an integral cubic remainder. If the scalar
vanishes in the residue field and two is a unit there, its quadratic coefficient
belongs to the maximal ideal.
-/

@[expose] public section

namespace FLT.Mazur
open IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- In odd residue characteristic, the quadratic coefficient of a vanishing scalar
lies in the maximal ideal. -/
theorem multiplicationSeries_coeff_two_mem (n : ℕ) (hn : (n : ResidueField A) = 0)
    (h2 : IsUnit (2 : ResidueField A)) :
    PowerSeries.coeff 2 (FormalInfinity.multiplicationSeries W n) ∈ maximalIdeal A := by
  apply (residue_eq_zero_iff _).mp
  have hm : PowerSeries.map (residue A) (FormalInfinity.multiplicationSeries W n) =
      FormalInfinity.multiplicationSeries (W.map (residue A)) n := by
    unfold FormalInfinity.multiplicationSeries PowerSeries.map
    rw [FormalInfinity.map_multiply W (residue A) n (by simp [PowerSeries.X])]
    simp only [PowerSeries.X, MvPowerSeries.map_X]
  have h := congrArg (PowerSeries.coeff 2) hm
  rw [PowerSeries.coeff_map,
    FormalInfinity.coeff_two_multiplicationSeries_eq_zero _ n hn h2] at h
  exact h

variable [IsAdicComplete (maximalIdeal A) A]

/-- The actual parameter has an integral cubic expansion with its formal quadratic coefficient. -/
theorem infinityParameter_nsmul_cubic_expansion (n : ℕ) (P : ellipticE1 A W) :
    ∃ r : A, infinityParameter A W (n • P) = n * infinityParameter A W P +
      PowerSeries.coeff 2 (FormalInfinity.multiplicationSeries W n) *
        infinityParameter A W P ^ 2 + infinityParameter A W P ^ 3 * r := by
  obtain ⟨g, hg⟩ := FormalInfinity.X_cube_dvd_multiplicationSeries_sub_quadratic W n
  have h := congrArg
    (localSeriesEvaluation A (infinityParameter A W P) (infinityParameter_mem A W P)) hg
  refine ⟨localSeriesEvaluation A (infinityParameter A W P) (infinityParameter_mem A W P) g, ?_⟩
  rw [infinityParameter_nsmul A W]
  simp only [map_sub, map_mul, map_pow, localSeriesEvaluation_C, localSeriesEvaluation_X] at h
  linear_combination h

end FLT.Mazur
