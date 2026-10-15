/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXLaurentEvaluation

/-!
# Both constructed Laurent branches of the original initial arithmetic chart

The same original coefficients construct both labeled slopes. Their
separation is a unit over the entire nonreduced Laurent boundary.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁) (hs : s ∈ I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "v₀" => nilpotentLaurentSlope W s b3 b4 b6 I hI ha hs h2 h3 h4 h6
local notation "a" => laurentSlopeLinear W b3
local notation "b" => laurentSlopeConstant W s b4 b6

/-- The original small Laurent root has invertible separation from its opposite. -/
theorem nilpotentLaurentSlope_simple : IsUnit (v₀ + v₀ + a) :=
  (NilpotentQuadraticRoot.element_nilpotent _ (laurentArithmeticIdeal_nilpotent I hI)
    ((laurentArithmeticIdeal I).add_mem
      (nilpotentLaurentSlope_mem W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)
      (nilpotentLaurentSlope_mem W s b3 b4 b6 I hI ha hs h2 h3 h4 h6))).isUnit_add_right_of_commute
    (laurentSlopeLinear_unit W b3 I hI ha h3) (mul_comm _ _)

/-- The two initial branches retain their ordered small and opposite labels. -/
def laurentBranchSlope (opposite : Bool) : R[T;T⁻¹] :=
  if opposite then QuadraticRootBranchLocalization.oppositeRoot a v₀ else v₀

/-- Both original initial branch slopes solve the unchanged Laurent quadratic. -/
theorem laurentBranchSlope_equation (opposite : Bool) :
    laurentBranchSlope W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 opposite ^ 2 +
      a * laurentBranchSlope W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 opposite = b := by
  cases opposite
  · exact nilpotentLaurentSlope_equation W s b3 b4 b6 I hI ha hs h2 h3 h4 h6
  · exact QuadraticRootBranchLocalization.oppositeRoot_equation a b v₀
      (nilpotentLaurentSlope_equation W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)

/-- Both ordered initial Laurent roots remain simple over every nilpotent thickening. -/
theorem laurentBranchSlope_simple (opposite : Bool) :
    IsUnit (laurentBranchSlope W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 opposite +
      laurentBranchSlope W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 opposite + a) := by
  cases opposite
  · exact nilpotentLaurentSlope_simple W s b3 b4 b6 I hI ha hs h2 h3 h4 h6
  · exact QuadraticRootBranchLocalization.oppositeRoot_simple a v₀
      (nilpotentLaurentSlope_simple W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)

/-- Both labeled initial branch maps are constructed from the original coefficients. -/
def laurentBranchEvaluation (opposite : Bool) : Coordinate W s b3 b4 b6 →ₐ[R] R[T;T⁻¹] :=
  laurentSlopeEvaluation W s b3 b4 b6
    (laurentBranchSlope W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 opposite)
    (laurentBranchSlope_equation W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 opposite)

end FLT.Mazur.WeierstrassModificationX
