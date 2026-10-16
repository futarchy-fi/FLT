/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingFirstLaurentLifts

/-!
# Positive incoming coefficients at a square-zero smoothing stage

The parameter kills every positive incoming coefficient of an original
node element. The exact parameter power is used before any reduction.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
open LaurentPolynomial
variable {R : Type*} [CommRing R] (t : R)

/-- Every positive incoming coefficient is killed by a square-zero parameter. -/
theorem parameter_precedingLaurentMap_positive (ht : t ^ 2 = 0)
    (z : ChartRing t) (k : ℤ) (hk : 0 < k) :
    t * (precedingLaurentMap R t z).coeff k = 0 := by
  by_cases he : k = 1
  · rw [he, show (1 : ℤ) = (1 : ℕ) by rfl, branch_coefficient_nonneg, pow_one,
      ← mul_assoc, ← pow_two, ht, zero_mul]
  · rw [precedingLaurentMap_coefficient_above t 1 ht z k (by omega), mul_zero]

end FLT.Mazur.PolygonSmoothing
