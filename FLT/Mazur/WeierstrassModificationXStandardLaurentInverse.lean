/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXStandardPunctureComparison
public import FLT.Mazur.LaurentUnitPoints

/-!
# Recover the original initial Laurent parameter on the complete puncture

The inverse original incidence defines an actual Laurent evaluation on D(p).
Its composite with the original boundary is the identity on every Laurent function.
-/

@[expose] public noncomputable section
open Polynomial
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁) (hs : s ∈ I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "N" => NodalFiber.Coordinate s
local notation "D" => Localization.Away (NodalFiber.p s)
local notation "L" => PolynomialNodeOpen W s
local notation "r₀" => polynomialSlopeRoot W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hr₀" => polynomialSlopeRoot_equation W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hm₀" => polynomialSlopeRoot_mem W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "P" => algebraMap N D (NodalFiber.p s)
local notation "Q" => algebraMap N D (NodalFiber.q s)
local notation "hu" => standardInitialPuncture_denominator_unit W s I hI ha hs
local notation "T" => polynomialNodeInverseT b3 r₀ I hI hm₀ h3 W P Q hu

local notation "F" => standardInitialEvaluation W s b3 b4 b6 I hI ha hs h2 h3 h4 h6
local notation "A" => initialNodeStandardPuncture W s I hI ha hs
local notation "F₀" => polynomialNodeForwardBase W s b3 b4 b6 r₀ hr₀ I hI hm₀ h3
local notation "P₀" => algebraMap N L (NodalFiber.p s)
local notation "Q₀" => algebraMap N L (NodalFiber.q s)
local notation "H" => laurentStandardPunctureEvaluation W s b3 b4 b6 I hI ha hs h2 h3 h4 h6

local notation "ht" => standardInitialEvaluation_t_unit W s b3 b4 b6 I hI ha hs h2 h3 h4 h6

/-- Recover the original Laurent parameter from the corrected original incidence on D(p). -/
def standardInitialLaurentInverse : R[T;T⁻¹] →ₐ[R] D :=
  LaurentUnitPoints.evalUnit ((ht).unit)⁻¹
local notation "K" => standardInitialLaurentInverse W s b3 b4 b6 I hI ha hs h2 h3 h4 h6

/-- The reciprocal Laurent coordinate is precisely the original corrected incidence. -/
theorem standardInitialLaurentInverse_reciprocal :
    K (LaurentPolynomial.T (-1)) = F (t W s b3 b4 b6) := by
  simp only [standardInitialLaurentInverse, LaurentUnitPoints.evalUnit_T, zpow_neg_one,
    inv_inv, IsUnit.unit_spec]

/-- The recovered original parameter evaluates back to the identity on the entire torus. -/
theorem laurentStandardPunctureEvaluation_inverse : (H).comp K = AlgHom.id R _ := by
  have hn : H (K (LaurentPolynomial.T (-1))) = LaurentPolynomial.T (-1) := by
    rw [standardInitialLaurentInverse_reciprocal]
    have h := DFunLike.congr_fun
      (laurentStandardPunctureEvaluation_initial W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)
      (t W s b3 b4 b6)
    exact h.trans (laurentSlopeEvaluation_t ..)
  apply LaurentUnitPoints.hom_ext
  · apply (LaurentPolynomial.isUnit_T (-1)).mul_right_cancel
    change H (K (LaurentPolynomial.T 1)) * LaurentPolynomial.T (-1) =
      LaurentPolynomial.T 1 * LaurentPolynomial.T (-1)
    calc
      _ = H (K (LaurentPolynomial.T 1 * LaurentPolynomial.T (-1))) := by
        rw [map_mul, map_mul, hn]
      _ = _ := by
        rw [← LaurentPolynomial.T_add]
        simp only [Int.reduceAdd, LaurentPolynomial.T_zero, map_one]
  · exact hn

end FLT.Mazur.WeierstrassModificationX
