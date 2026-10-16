/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXLaurentNodeRestriction

/-!
# The original initial boundary when the arithmetic ideal is zero

Both constructed small roots are then zero. Consequently the original first
node coordinate is a₁T⁻¹ and the second is zero. This is an exact zero-fiber
calculation, not a replacement for the full nilpotent correction.
-/

@[expose] public noncomputable section
open Polynomial
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁) (hs : s ∈ I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I) (hbot : I = ⊥)
local notation "r₀" => polynomialSlopeRoot W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "v₀" => nilpotentLaurentSlope W s b3 b4 b6 I hI ha hs h2 h3 h4 h6
local notation "E" => laurentBranchEvaluation W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 false
local notation "G" => laurentNodeRestriction W s b3 b4 b6 I hI ha hs h2 h3 h4 h6
local notation "N" => NodalFiber.Coordinate s
local notation "L" => PolynomialNodeOpen W s

include hbot

/-- The constructed polynomial small root vanishes when its arithmetic ideal vanishes. -/
theorem polynomialSlopeRoot_eq_zero_of_bot : r₀ = 0 := by
  have h := polynomialSlopeRoot_mem W b3 b4 b6 I hI ha h2 h3 h4 h6
  simpa only [polynomialArithmeticIdeal, hbot, Ideal.map_bot, Ideal.mem_bot] using h

/-- The constructed Laurent small root also vanishes over the zero arithmetic ideal. -/
theorem nilpotentLaurentSlope_eq_zero_of_bot : v₀ = 0 := by
  have h := nilpotentLaurentSlope_mem W s b3 b4 b6 I hI ha hs h2 h3 h4 h6
  simpa only [laurentArithmeticIdeal, hbot, Ideal.map_bot, Ideal.mem_bot] using h

/-- The small factor is exactly zero on this original zero-fiber boundary. -/
theorem laurentBranchEvaluation_small_of_bot :
    E (polynomialSmallFactor W s b3 b4 b6 r₀) = 0 := by
  rw [polynomialSmallFactor, polynomialSlopeRoot_eq_zero_of_bot W b3 b4 b6 I hI
    ha h2 h3 h4 h6 hbot, map_zero, sub_zero]
  simp only [laurentBranchEvaluation, laurentSlopeEvaluation_v, laurentBranchSlope,
    Bool.false_eq_true, ↓reduceIte]
  exact nilpotentLaurentSlope_eq_zero_of_bot W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 hbot

/-- The opposite factor on the original boundary is precisely the tangent unit. -/
theorem laurentBranchEvaluation_opposite_of_bot :
    E (polynomialOppositeFactor W s b3 b4 b6 r₀) = LaurentPolynomial.C W.a₁ := by
  have h30 : b3 = 0 := Ideal.mem_bot.mp (hbot ▸ h3)
  rw [polynomialOppositeFactor, polynomialSlopeRoot_eq_zero_of_bot W b3 b4 b6 I hI
    ha h2 h3 h4 h6 hbot, zero_add, map_add, hom_polynomial_incidence]
  simp only [laurentBranchEvaluation, laurentSlopeEvaluation_v, laurentSlopeEvaluation_t,
    laurentBranchSlope,
    Bool.false_eq_true, ↓reduceIte]
  rw [nilpotentLaurentSlope_eq_zero_of_bot W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 hbot]
  simp only [polynomialSlopeLinear, h30, map_zero, zero_mul, add_zero,
    eval₂_C, zero_add]
  exact (LaurentPolynomial.C_eq_algebraMap W.a₁).symm

/-- The original first node parameter has only its constant tangent-unit correction. -/
theorem laurentNodeRestriction_p_of_bot :
    G (algebraMap N L (NodalFiber.p s)) =
      LaurentPolynomial.T (-1) * LaurentPolynomial.C W.a₁ := by
  rw [laurentNodeRestriction_p, laurentBranchEvaluation_opposite_of_bot W s b3 b4 b6 I
    hI ha hs h2 h3 h4 h6 hbot]

/-- The original second node parameter is exactly zero on this boundary. -/
theorem laurentNodeRestriction_q_of_bot : G (algebraMap N L (NodalFiber.q s)) = 0 := by
  rw [laurentNodeRestriction_q, laurentBranchEvaluation_small_of_bot W s b3 b4 b6 I
    hI ha hs h2 h3 h4 h6 hbot]

end FLT.Mazur.WeierstrassModificationX
