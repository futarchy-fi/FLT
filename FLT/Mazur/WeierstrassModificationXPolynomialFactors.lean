/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXPolynomialRoot

/-!
# The two full arithmetic tangent factors

The polynomial root factors the original horizontal function on the entire
initial chart. Their difference is a unit over every nilpotent arithmetic base.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
local notation "A" => Coordinate W s b3 b4 b6
local notation "f" => algebraMap R[X] A

/-- The small tangent factor on the entire original initial chart. -/
def polynomialSmallFactor : A := v W s b3 b4 b6 - f r

/-- The opposite tangent factor on the entire original initial chart. -/
def polynomialOppositeFactor : A := v W s b3 b4 b6 + f (r + polynomialSlopeLinear W b3)

include hr in
/-- Evaluation at the original t retains the full conic root equation. -/
theorem polynomialRoot_originalEquation :
    f r ^ 2 + (algebraMap R A W.a₁ + algebraMap R A b3 * t W s b3 b4 b6) * f r =
      algebraMap R A W.a₂ + algebraMap R A b4 * t W s b3 b4 b6 +
        algebraMap R A b6 * t W s b3 b4 b6 ^ 2 := by
  have h := congrArg f hr
  have hc (z : R) : f (C z) = algebraMap R A z :=
    (IsScalarTower.algebraMap_apply R R[X] A z).symm
  simpa only [polynomialSlopeLinear, polynomialSlopeConstant, map_add, map_mul, map_pow,
    hc, t] using h

include hr in
/-- The complete original horizontal function is the product of the constructed factors. -/
theorem polynomialFactors_horizontal :
    x W s b3 b4 b6 = polynomialSmallFactor W s b3 b4 b6 r *
      polynomialOppositeFactor W s b3 b4 b6 r := by
  have h := polynomialRoot_originalEquation W s b3 b4 b6 r hr
  simp only [x, polynomialSmallFactor, polynomialOppositeFactor, polynomialSlopeLinear,
    map_add, map_mul]
  change _ = (v W s b3 b4 b6 - f r) *
    (v W s b3 b4 b6 + (f r + (algebraMap R A W.a₁ +
      algebraMap R A b3 * t W s b3 b4 b6)))
  linear_combination h

include hr in
/-- The full factorization retains the actual smoothing scale at t=0 as well. -/
theorem polynomialFactors_incidence :
    t W s b3 b4 b6 * (polynomialSmallFactor W s b3 b4 b6 r *
      polynomialOppositeFactor W s b3 b4 b6 r) = algebraMap R A s := by
  rw [← polynomialFactors_horizontal W s b3 b4 b6 r hr]
  exact incidence W s b3 b4 b6

/-- The separation of the two factors is a function of the incidence coordinate alone. -/
theorem polynomialFactors_difference :
    polynomialOppositeFactor W s b3 b4 b6 r - polynomialSmallFactor W s b3 b4 b6 r =
      f (r + r + polynomialSlopeLinear W b3) := by
  simp only [polynomialSmallFactor, polynomialOppositeFactor, map_add]
  ring

variable (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "r₀" => polynomialSlopeRoot W b3 b4 b6 I hI ha h2 h3 h4 h6

/-- The polynomial small and opposite roots have unit separation on the full incidence line. -/
theorem polynomialSlopeRoot_simple :
    IsUnit (r₀ + r₀ + polynomialSlopeLinear W b3) :=
  (NilpotentQuadraticRoot.element_nilpotent _ (polynomialArithmeticIdeal_nilpotent I hI)
    ((polynomialArithmeticIdeal I).add_mem
      (polynomialSlopeRoot_mem W b3 b4 b6 I hI ha h2 h3 h4 h6)
      (polynomialSlopeRoot_mem W b3 b4 b6 I hI ha h2 h3 h4 h6))).isUnit_add_right_of_commute
    (polynomialSlopeLinear_unit W b3 I hI ha h3) (mul_comm _ _)

/-- The full original arithmetic chart retains unit separation of its two tangent factors. -/
theorem polynomialFactors_difference_unit :
    IsUnit (polynomialOppositeFactor W s b3 b4 b6 r₀ -
      polynomialSmallFactor W s b3 b4 b6 r₀) := by
  rw [polynomialFactors_difference]
  exact (polynomialSlopeRoot_simple W b3 b4 b6 I hI ha h2 h3 h4 h6).map f

end FLT.Mazur.WeierstrassModificationX
