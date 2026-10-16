/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXPolynomialCoefficientNaturality
public import FLT.Mazur.WeierstrassModificationXLaurentCoefficientNaturality
public import FLT.Mazur.WeierstrassModificationXLaurentNodeDenominator

/-!
# Coefficient change preserves the complete initial Laurent tangent factors

The original incidence is reciprocal Laurent T. Both polynomial corrections
and both branch labels survive coefficient restriction on this full boundary.
-/

@[expose] public noncomputable section
open Polynomial
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
local notation "F" => PolygonScalingNaturality.coeffMap f

/-- Polynomial evaluation at the original reciprocal parameter preserves coefficients. -/
theorem laurentPolynomialEvaluation_coefficient (r : R[X]) :
    F (r.eval₂ (algebraMap R R[T;T⁻¹]) (LaurentPolynomial.T (-1))) =
      (r.map f).eval₂ (algebraMap S S[T;T⁻¹]) (LaurentPolynomial.T (-1)) := by
  have hc : (F).comp (algebraMap R R[T;T⁻¹]) =
      (algebraMap S S[T;T⁻¹]).comp f :=
    RingHom.ext (PolygonScalingNaturality.coeffMap_C f)
  simpa only [aeval_def, PolygonScalingNaturality.coeffMap_T_neg_one] using
    (Polynomial.map_aeval_eq_aeval_map hc.symm r (LaurentPolynomial.T (-1)))

variable (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (I : Ideal R) (J : Ideal S) (hf : I ≤ J.comap f)
  (hI : IsNilpotent I) (hJ : IsNilpotent J)
  (ha : IsUnit W.a₁) (hs : s ∈ I) (h2 : W.a₂ ∈ I)
  (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I) (opposite : Bool)
local notation "U" => W.map f
local notation "r₀" => polynomialSlopeRoot W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "r₁" => polynomialSlopeRoot U (f b3) (f b4) (f b6) J hJ
  (ha.map f) (hf h2) (hf h3) (hf h4) (hf h6)
local notation "E₀" => laurentBranchEvaluation W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 opposite
local notation "E₁" => laurentBranchEvaluation U (f s) (f b3) (f b4) (f b6) J hJ
  (ha.map f) (hf hs) (hf h2) (hf h3) (hf h4) (hf h6) opposite

/-- The full small tangent factor retains every polynomial correction and either branch label. -/
theorem laurentSmallFactor_coefficient :
    F (E₀ (polynomialSmallFactor W s b3 b4 b6 r₀)) =
      E₁ (polynomialSmallFactor U (f s) (f b3) (f b4) (f b6) r₁) := by
  simp only [polynomialSmallFactor, map_sub, hom_polynomial_incidence]
  simp only [laurentBranchEvaluation, laurentSlopeEvaluation_t, laurentSlopeEvaluation_v]
  rw [laurentBranchSlope_coefficient f W s b3 b4 b6 I J hf hI hJ ha hs h2 h3 h4 h6,
    laurentPolynomialEvaluation_coefficient]
  exact congrArg (fun r ↦ _ - Polynomial.eval₂ (algebraMap S S[T;T⁻¹])
    (LaurentPolynomial.T (-1)) r)
    (polynomialSlopeRoot_coefficient f W b3 b4 b6 I J hf hI hJ ha h2 h3 h4 h6)

/-- The complete opposite tangent factor has the same original coefficient transport. -/
theorem laurentOppositeFactor_coefficient :
    F (E₀ (polynomialOppositeFactor W s b3 b4 b6 r₀)) =
      E₁ (polynomialOppositeFactor U (f s) (f b3) (f b4) (f b6) r₁) := by
  simp only [polynomialOppositeFactor, map_add, hom_polynomial_incidence]
  simp only [laurentBranchEvaluation, laurentSlopeEvaluation_t, laurentSlopeEvaluation_v]
  rw [laurentBranchSlope_coefficient f W s b3 b4 b6 I J hf hI hJ ha hs h2 h3 h4 h6,
    laurentPolynomialEvaluation_coefficient]
  have hr := polynomialSlopeRoot_coefficient f W b3 b4 b6 I J hf hI hJ ha h2 h3 h4 h6
  have hl := polynomialSlopeLinear_coefficient f W b3
  change Polynomial.map f r₀ = r₁ at hr
  change Polynomial.map f (polynomialSlopeLinear W b3) = _ at hl
  rw [hr, laurentPolynomialEvaluation_coefficient, hl]

end FLT.Mazur.WeierstrassModificationX
