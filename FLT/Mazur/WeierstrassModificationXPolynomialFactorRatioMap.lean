/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFactorRatioMap
public import FLT.Mazur.WeierstrassModificationXNodeIncidenceOpen

/-!
# Constructed factor-ratio map on the whole original initial node

The opposite-factor unit is supplied by the original polynomial node construction.
The resulting map is defined on the entire node neighborhood, including t=0.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s τ : R) (hτ : s = W.a₁ ^ 2 * τ) (b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "L" => PolynomialNodeOpen W s
local notation "M" => NodalFiber.TangentOpen τ (-1 : R)
local notation "G" => polynomialNodeForwardBase W s b3 b4 b6 r hr I hI hrI h3
local notation "hu" => polynomialNodeForwardBase_opposite_isUnit W s b3 b4 b6 r hr I hI hrI h3
local notation "U" => G (polynomialOppositeFactor W s b3 b4 b6 r)
local notation "V" => G (polynomialSmallFactor W s b3 b4 b6 r)

/-- The corrected full normalized map uses the independently constructed original factors. -/
def polynomialFactorRatioMap : M →ₐ[R] L :=
  initialFactorRatioMap W ha s τ hτ b3 b4 b6 r hr G hu I hI hrI h3

local notation "F" => polynomialFactorRatioMap W ha s τ hτ b3 b4 b6 r hr I hI hrI h3

/-- The corrected first coordinate retains the entire original incidence and factor square. -/
theorem polynomialFactorRatioMap_p :
    F (NodalFiber.tangentP τ (-1 : R)) =
      algebraMap R L (↑(zeroInitialTangentUnit W ha)⁻¹ : R) ^ 2 *
        G (t W s b3 b4 b6) * U ^ 2 := by
  rw [polynomialFactorRatioMap, NodalFiber.tangentP, initialFactorRatioMap_base]
  exact NodalFiber.evaluation_p ..

/-- The second corrected coordinate is the full original factor ratio. -/
theorem polynomialFactorRatioMap_q :
    F (NodalFiber.tangentQ τ (-1 : R)) = V * ↑(hu).unit⁻¹ := by
  rw [polynomialFactorRatioMap, NodalFiber.tangentQ, initialFactorRatioMap_base]
  exact NodalFiber.evaluation_q ..

/-- The full corrected second coordinate has exactly the actual original opposite denominator. -/
theorem polynomialFactorRatioMap_q_denominator :
    F (NodalFiber.tangentQ τ (-1 : R)) * U = V := by
  rw [polynomialFactorRatioMap_q, mul_assoc, (hu).val_inv_mul, mul_one]

/-- The corrected first coordinate is original p times the entire opposite correction over a². -/
theorem polynomialFactorRatioMap_p_node :
    F (NodalFiber.tangentP τ (-1 : R)) =
      algebraMap R L (↑(zeroInitialTangentUnit W ha)⁻¹ : R) ^ 2 *
        NodalFiber.tangentP s W.a₁ * U := by
  have hp : G (t W s b3 b4 b6) * U = NodalFiber.tangentP s W.a₁ := by
    rw [← map_mul]
    exact polynomialNodeEvaluation_first ..
  rw [polynomialFactorRatioMap_p, pow_two U]
  calc
    _ = algebraMap R L (↑(zeroInitialTangentUnit W ha)⁻¹ : R) ^ 2 *
        (G (t W s b3 b4 b6) * U) * U := by ring
    _ = _ := by rw [hp]

end FLT.Mazur.WeierstrassModificationX
