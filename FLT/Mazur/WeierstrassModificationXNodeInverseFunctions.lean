/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeInverseEvaluation

/-!
# Recovering the original node coordinates on all initial functions

The constructed evaluation preserves both full tangent factors and sends
the corrected incidence and small factor to the prescribed node coordinates.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
local notation "A" => Coordinate W s b3 b4 b6

/-- Every polynomial incidence function is transported by evaluating at the image of t. -/
theorem hom_polynomial_incidence (g : A →ₐ[R] S) (r : R[X]) :
    g (algebraMap R[X] A r) = r.eval₂ (algebraMap R S) (g (t W s b3 b4 b6)) :=
  (Polynomial.eval₂_algebraMap_X r (g.comp (Algebra.algHom R R[X] A))).symm

variable (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
  (p q : S) (hu : IsUnit (q + algebraMap R S W.a₁)) (hpq : p * q = algebraMap R S s)
local notation "T" => polynomialNodeInverseT b3 r I hI hrI h3 W p q hu
local notation "E" => polynomialNodeEvaluation W s b3 b4 b6 r hr I hI hrI h3 p q hu hpq
local notation "f" => algebraMap R S

/-- The original small factor is exactly the second node coordinate. -/
theorem polynomialNodeEvaluation_small : E (polynomialSmallFactor W s b3 b4 b6 r) = q := by
  rw [polynomialSmallFactor, map_sub, polynomialNodeEvaluation_v,
    hom_polynomial_incidence, polynomialNodeEvaluation_t, add_sub_cancel_right]

/-- The opposite factor retains the complete polynomial correction. -/
theorem polynomialNodeEvaluation_opposite :
    E (polynomialOppositeFactor W s b3 b4 b6 r) =
      q + f W.a₁ + (r.eval₂ f T + r.eval₂ f T + f b3 * T) := by
  rw [polynomialOppositeFactor, map_add, polynomialNodeEvaluation_v,
    hom_polynomial_incidence, polynomialNodeEvaluation_t]
  simp only [polynomialSlopeLinear, eval₂_add, eval₂_mul, eval₂_C, eval₂_X]
  ring

/-- The corrected original incidence is exactly the first node coordinate. -/
theorem polynomialNodeEvaluation_first :
    E (t W s b3 b4 b6 * polynomialOppositeFactor W s b3 b4 b6 r) = p := by
  rw [map_mul, polynomialNodeEvaluation_t, polynomialNodeEvaluation_opposite]
  exact polynomialNodeInverseT_equation b3 r I hI hrI h3 W p q hu

end FLT.Mazur.WeierstrassModificationX
