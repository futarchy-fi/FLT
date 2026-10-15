/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXLaurentNodeRestriction

/-!
# The actual initial Laurent parameter in full node coordinates

The first node coordinate is an invertible correction of the inverse original
Laurent parameter. The second is nilpotent, and their product is the original scale.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁) (hs : s ∈ I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "B" => R[T;T⁻¹]
local notation "L" => PolynomialNodeOpen W s
local notation "N" => NodalFiber.Coordinate s
local notation "G" => laurentNodeRestriction W s b3 b4 b6 I hI ha hs h2 h3 h4 h6
local notation "E" => laurentBranchEvaluation W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 false
local notation "r₀" => polynomialSlopeRoot W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hm₀" => polynomialSlopeRoot_mem W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "v₀" => nilpotentLaurentSlope W s b3 b4 b6 I hI ha hs h2 h3 h4 h6
local notation "P" => algebraMap N L (NodalFiber.p s)
local notation "Q" => algebraMap N L (NodalFiber.q s)

/-- The node's small coordinate retains the small Laurent label modulo the arithmetic ideal. -/
theorem laurentNodeRestriction_q_mem : G Q ∈ laurentArithmeticIdeal I := by
  rw [laurentNodeRestriction_q, polynomialSmallFactor, map_sub, hom_polynomial_incidence]
  rw [show E (v W s b3 b4 b6) = v₀ from laurentSlopeEvaluation_v ..]
  change v₀ - (r₀).eval₂ (algebraMap R B) (E (t W s b3 b4 b6)) ∈ laurentArithmeticIdeal I
  exact (laurentArithmeticIdeal I).sub_mem
    (nilpotentLaurentSlope_mem W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)
    (NilpotentPolynomialInverse.eval₂_mem I (algebraMap R B) r₀ hm₀ _)

/-- The entire Laurent boundary lies on the nilpotent small branch of the full node. -/
theorem laurentNodeRestriction_q_nilpotent : IsNilpotent (G Q) :=
  NilpotentQuadraticRoot.element_nilpotent _ (laurentArithmeticIdeal_nilpotent I hI)
    (laurentNodeRestriction_q_mem W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)

/-- The full opposite factor is a unit along the original small Laurent boundary. -/
theorem laurentNodeRestriction_opposite_unit :
    IsUnit (E (polynomialOppositeFactor W s b3 b4 b6 r₀)) := by
  rw [polynomialOppositeFactor, map_add, hom_polynomial_incidence]
  rw [show E (v W s b3 b4 b6) = v₀ from laurentSlopeEvaluation_v ..]
  change IsUnit (v₀ + (r₀ + polynomialSlopeLinear W b3).eval₂ (algebraMap R B)
    (E (t W s b3 b4 b6)))
  simp only [polynomialSlopeLinear, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X]
  have hn : v₀ + (r₀).eval₂ (algebraMap R B) (E (t W s b3 b4 b6)) +
      algebraMap R B b3 * E (t W s b3 b4 b6) ∈ laurentArithmeticIdeal I :=
    (laurentArithmeticIdeal I).add_mem ((laurentArithmeticIdeal I).add_mem
      (nilpotentLaurentSlope_mem W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)
      (NilpotentPolynomialInverse.eval₂_mem I (algebraMap R B) r₀ hm₀ _))
      ((laurentArithmeticIdeal I).mul_mem_right _ (Ideal.mem_map_of_mem _ h3))
  have hu := (NilpotentQuadraticRoot.element_nilpotent _
    (laurentArithmeticIdeal_nilpotent I hI) hn).isUnit_add_right_of_commute
      (ha.map (algebraMap R B)) (mul_comm _ _)
  convert hu using 1
  ring

/-- The first node coordinate is invertible on the entire original Laurent boundary. -/
theorem laurentNodeRestriction_p_unit : IsUnit (G P) := by
  rw [laurentNodeRestriction_p]
  exact (LaurentPolynomial.isUnit_T (-1)).mul
    (laurentNodeRestriction_opposite_unit W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)

/-- The corrected node parameters retain the original smoothing scale exactly. -/
theorem laurentNodeRestriction_relation : G P * G Q = algebraMap R B s := by
  rw [← map_mul, polynomialNodeOpen_relation, AlgHom.commutes]

end FLT.Mazur.WeierstrassModificationX
