/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXPolynomialFactorRatioEquiv
public import FLT.Mazur.WeierstrassModificationXInitialMobiusLaurentReduction

/-!
# The exact corrected factor-ratio Laurent parameter

The retained first coordinate is a⁻² T⁻¹ E(U)². It is a unit and differs from
T⁻¹ by the original arithmetic ideal, with both opposite-factor corrections retained.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s : R) (b3 b4 b6 : R) (I : Ideal R) (hI : IsNilpotent I) (hs : s ∈ I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "a" => zeroInitialTangentUnit W ha
local notation "B" => R[T;T⁻¹]
local notation "J" => laurentArithmeticIdeal I
local notation "E" => laurentBranchEvaluation W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 false
local notation "r₀" => polynomialSlopeRoot W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hr₀" => polynomialSlopeRoot_equation W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hm₀" => polynomialSlopeRoot_mem W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "G" => laurentNodeRestriction W s b3 b4 b6 I hI ha hs h2 h3 h4 h6
local notation "F" => polynomialNodeForwardBase W s b3 b4 b6 r₀ hr₀ I hI hm₀ h3
local notation "U" => E (polynomialOppositeFactor W s b3 b4 b6 r₀)
local notation "Ai" => algebraMap R B (↑a⁻¹ : R)
local notation "A" => algebraMap R B W.a₁

/-- The full retained factor square is invertible along the original Laurent boundary. -/
theorem factorRatioLaurent_isUnit : IsUnit (Ai ^ 2 * LaurentPolynomial.T (-1) * U ^ 2) :=
  (((a⁻¹.isUnit.map (algebraMap R B)).pow 2).mul (LaurentPolynomial.isUnit_T (-1))).mul
    ((laurentNodeRestriction_opposite_unit W s b3 b4 b6 I hI ha hs h2 h3 h4 h6).pow 2)

/-- The original boundary parameter for the corrected full factor-ratio map. -/
def factorRatioLaurentUnit : Bˣ :=
  (factorRatioLaurent_isUnit W ha s b3 b4 b6 I hI hs h2 h3 h4 h6).unit

local notation "u" => factorRatioLaurentUnit W ha s b3 b4 b6 I hI hs h2 h3 h4 h6

/-- The exact retained parameter contains the full square of the opposite factor. -/
theorem factorRatioLaurentUnit_coe : (u : B) = Ai ^ 2 * LaurentPolynomial.T (-1) * U ^ 2 :=
  (factorRatioLaurent_isUnit W ha s b3 b4 b6 I hI hs h2 h3 h4 h6).unit_spec

/-- The new retained coordinate is an inverse-coordinate perturbation in the original ideal. -/
theorem factorRatioLaurentUnit_sub_mem : (u : B) - LaurentPolynomial.T (-1) ∈ J := by
  rw [factorRatioLaurentUnit_coe]
  have he := (J).mul_mem_left (Ai ^ 2 * LaurentPolynomial.T (-1) * (U + A))
    (laurentNodeRestriction_opposite_sub_mem W ha s b3 b4 b6 I hI hs h2 h3 h4 h6)
  have hi : Ai * A = 1 := by
    rw [← map_mul, show (↑a⁻¹ : R) * W.a₁ = 1 from (a).inv_mul, map_one]
  convert he using 1
  linear_combination LaurentPolynomial.T (-1) * (Ai * A + 1) * hi

/-- The new unit is the pullback of the corrected first coordinate on the whole original node. -/
theorem factorRatioLaurentUnit_coordinate (τ : R) (hτ : s = W.a₁ ^ 2 * τ) :
    G (polynomialFactorRatioMap W ha s τ hτ b3 b4 b6 r₀ hr₀ I hI hm₀ h3
      (NodalFiber.tangentP τ (-1 : R))) = (u : B) := by
  rw [polynomialFactorRatioMap_p_node, map_mul, map_mul, map_pow, AlgHom.commutes]
  have hu : G (F (polynomialOppositeFactor W s b3 b4 b6 r₀)) = U :=
    congrArg (fun k ↦ k (polynomialOppositeFactor W s b3 b4 b6 r₀))
      (laurentNodeRestriction_first W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)
  rw [hu]
  change Ai ^ 2 * G (algebraMap _ _ (NodalFiber.p s)) * U = _
  rw [laurentNodeRestriction_p, factorRatioLaurentUnit_coe]
  ring

end FLT.Mazur.WeierstrassModificationX
