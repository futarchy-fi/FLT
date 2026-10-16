/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeInverseFunctions
public import FLT.Mazur.NilpotentPolynomialEvaluation

/-!
# The full original tangent-factor gap is a unit

For every evaluation of the original initial chart, the two polynomial factors
differ by the tangent coefficient plus a nilpotent arithmetic correction.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R) (r : R[X])
  (I : Ideal R) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
  (g : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "U" => g (polynomialOppositeFactor W s b3 b4 b6 r)
local notation "V" => g (polynomialSmallFactor W s b3 b4 b6 r)
local notation "a" => algebraMap R S W.a₁
local notation "J" => I.map (algebraMap R S)

/-- The exact factor-gap correction retains both polynomial-root terms and divided b3. -/
theorem evaluatedFactorGap_eq : U - V - a =
    r.eval₂ (algebraMap R S) (g (t W s b3 b4 b6)) +
      r.eval₂ (algebraMap R S) (g (t W s b3 b4 b6)) +
        algebraMap R S b3 * g (t W s b3 b4 b6) := by
  simp only [polynomialOppositeFactor, polynomialSmallFactor, map_add, map_sub,
    hom_polynomial_incidence, polynomialSlopeLinear,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
  ring

include hrI h3 in
/-- The entire correction lies in the extended original coefficient ideal. -/
theorem evaluatedFactorGap_mem : U - V - a ∈ J := by
  rw [evaluatedFactorGap_eq]
  have hr := NilpotentPolynomialInverse.eval₂_mem I (algebraMap R S) r hrI
    (g (t W s b3 b4 b6))
  exact (J).add_mem ((J).add_mem hr hr)
    ((J).mul_mem_right _ (Ideal.mem_map_of_mem _ h3))

include hrI h3 in
/-- Nilpotent arithmetic corrections preserve the full original tangent-factor separation. -/
theorem evaluatedFactorGap_isUnit (hI : IsNilpotent I) (ha : IsUnit W.a₁) : IsUnit (U - V) := by
  have hn := NilpotentQuadraticRoot.element_nilpotent J
    (NilpotentPolynomialInverse.mapIdeal_nilpotent I hI (algebraMap R S))
    (evaluatedFactorGap_mem W s b3 b4 b6 r I hrI h3 g)
  have hu := hn.isUnit_add_left_of_commute (ha.map (algebraMap R S)) (mul_comm _ _)
  convert hu using 1
  ring

end FLT.Mazur.WeierstrassModificationX
