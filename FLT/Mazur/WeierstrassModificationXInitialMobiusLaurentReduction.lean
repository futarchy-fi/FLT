/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXInitialMobiusLaurentBoundary
public import FLT.Mazur.WeierstrassModificationXInitialMobiusNormalization

/-!
# Arithmetic congruence of the full fractional retained parameter

The entire opposite factor and translated smoothing are retained. Their
correction to the inverse Laurent parameter lies in the original coefficient ideal.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s τ : R) (hτ : s = W.a₁ ^ 2 * τ) (b3 b4 b6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (hs : s ∈ I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "a" => zeroInitialTangentUnit W ha
local notation "B" => R[T;T⁻¹]
local notation "J" => laurentArithmeticIdeal I
local notation "E" => laurentBranchEvaluation W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 false
local notation "r₀" => polynomialSlopeRoot W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "v₀" => nilpotentLaurentSlope W s b3 b4 b6 I hI ha hs h2 h3 h4 h6

include hτ in
/-- The specified normalized smoothing is the one constructed from the tangent unit. -/
theorem initialMobius_smoothing_eq : τ = initialTangentSmoothing W ha s := by
  have hi : (↑a⁻¹ : R) * W.a₁ = 1 := (a).inv_mul
  rw [initialTangentSmoothing, hτ]
  calc
    τ = 1 ^ 2 * τ := by ring
    _ = ((↑a⁻¹ : R) * W.a₁) ^ 2 * τ := by rw [hi]
    _ = (↑a⁻¹ : R) ^ 2 * (W.a₁ ^ 2 * τ) := by ring

include ha hτ hs in
/-- Tangent normalization preserves the original arithmetic ideal, not only nilpotence. -/
theorem initialMobius_smoothing_mem : τ ∈ I := by
  rw [initialMobius_smoothing_eq W ha s τ hτ, initialTangentSmoothing]
  exact I.mul_mem_left _ hs

/-- The full evaluated opposite factor reduces to the actual tangent coefficient. -/
theorem laurentNodeRestriction_opposite_sub_mem :
    E (polynomialOppositeFactor W s b3 b4 b6 r₀) - algebraMap R B W.a₁ ∈ J := by
  rw [polynomialOppositeFactor, map_add, hom_polynomial_incidence]
  rw [show E (v W s b3 b4 b6) = v₀ from laurentSlopeEvaluation_v ..]
  change v₀ + (r₀ + polynomialSlopeLinear W b3).eval₂ (algebraMap R B)
    (E (t W s b3 b4 b6)) - algebraMap R B W.a₁ ∈ J
  simp only [polynomialSlopeLinear, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X]
  have hr := NilpotentPolynomialInverse.eval₂_mem I (algebraMap R B) r₀
    (polynomialSlopeRoot_mem W b3 b4 b6 I hI ha h2 h3 h4 h6)
    (E (t W s b3 b4 b6))
  have hb : algebraMap R B b3 * E (t W s b3 b4 b6) ∈ J :=
    (J).mul_mem_right _ (Ideal.mem_map_of_mem _ h3)
  convert (J).add_mem ((J).add_mem
    (nilpotentLaurentSlope_mem W s b3 b4 b6 I hI ha hs h2 h3 h4 h6) hr) hb using 1
  ring

/-- The exact fractional Laurent unit is an inverse-coordinate perturbation in the base ideal. -/
theorem initialMobiusLaurentUnit_sub_mem :
    (initialMobiusLaurentUnit W ha s τ hτ b3 b4 b6 I hI hs h2 h3 h4 h6 : B) -
      LaurentPolynomial.T (-1) ∈ J := by
  rw [initialMobiusLaurentUnit_coe]
  have h := (J).mul_mem_left
    (algebraMap R B (↑a⁻¹ : R) * LaurentPolynomial.T (-1))
    (laurentNodeRestriction_opposite_sub_mem W ha s b3 b4 b6 I hI hs h2 h3 h4 h6)
  have ht : algebraMap R B τ ∈ J := Ideal.mem_map_of_mem _
    (initialMobius_smoothing_mem W ha s τ hτ I hs)
  have hi : algebraMap R B (↑a⁻¹ : R) * algebraMap R B W.a₁ = 1 := by
    rw [← map_mul, show (↑a⁻¹ : R) * W.a₁ = 1 from (a).inv_mul, map_one]
  convert (J).add_mem h ht using 1
  linear_combination LaurentPolynomial.T (-1) * hi

end FLT.Mazur.WeierstrassModificationX
