/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSplitLocalizedImages
public import FLT.Mazur.PolygonNodeEqualizerComparison

/-!
# The split refinement denominator does not vanish at the node

Clear the Laurent coordinate on the punctured branch, descend the resulting
polynomial equation faithfully, then evaluate on the unpunctured branch.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open scoped LaurentPolynomial
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonSplitCubicCoordinates
open PolygonPinching PolygonNodeAffineCharts PolygonNodeEqualizer PolygonNodeLocalization
open PolygonNodePresentation PolygonCubicSections LocalizationJointRestriction
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ) (hn₂ : 2 ≤ n) (i : Fin n) (z : Spec (.of K))

local notation "s" => splitDenominator K n hn p q h a hn₂ i z
local notation "c" => coordinate K n hn p q h a hn₂ i z i 0

/-- The unpunctured left normalization satisfies the denominator-cleared equation. -/
lemma left_polynomial_equation :
    NodeDenominatorRestriction.left s c *
      algebraMap K[X] (Localization.Away (first s)) ((X - Polynomial.C (a i : K)) ^ 3) = 1 := by
  apply restriction_injective (Polynomial.toLaurent : K[X] →+* LaurentPolynomial K)
    (first s) Polynomial.toLaurent_injective
  rw [map_mul, map_one, restriction_algebraMap]
  change NodePuncturedDenominatorRestriction.left s c *
    algebraMap (LaurentPolynomial K) (Localization.Away (first s).toLaurent)
      (Polynomial.toLaurent ((X - Polynomial.C (a i : K)) ^ 3)) = 1
  have he := split_left_interpolation_equation K n hn p q h a hn₂ i z i 0
  dsimp only at he
  rw [split_numerator_left_node K n a hn₂ i,
    PuncturedNodeRestrictionComparison.left_eq] at he
  change NodePuncturedDenominatorRestriction.left s c *
    algebraMap (LaurentPolynomial K) (Localization.Away (first s).toLaurent)
      ((LaurentPolynomial.T 1 - LaurentPolynomial.C (a i : K)) ^ 3 *
        LaurentPolynomial.T (-1)) =
      algebraMap (LaurentPolynomial K) (Localization.Away (first s).toLaurent)
        (LaurentPolynomial.T (-1)) at he
  have ht : IsUnit (algebraMap (LaurentPolynomial K) (Localization.Away (first s).toLaurent)
      (LaurentPolynomial.T (-1))) :=
    (LaurentPolynomial.isUnit_T (-1)).map _
  apply ht.mul_right_cancel
  rw [one_mul, mul_assoc, ← map_mul]
  simpa only [map_pow, map_sub, Polynomial.toLaurent_X, Polynomial.toLaurent_C]
    using he

/-- Evaluation at the retained split origin on the exact original localization. -/
def nodeEvaluation : Localization.Away s →+* K :=
  (NodeDenominatorEqualizer.evalLeft s
    (splitDenominator_value_isUnit K n hn p q h a hn₂ i z)).comp
      (NodeDenominatorRestriction.left s)

/-- The node-value coordinate times the nonzero marked-point factor is one. -/
lemma nodeEvaluation_coordinate :
    nodeEvaluation K n hn p q h a hn₂ i z c * (-(a i : K)) ^ 3 = 1 := by
  have he := congrArg (NodeDenominatorEqualizer.evalLeft s
    (splitDenominator_value_isUnit K n hn p q h a hn₂ i z))
      (left_polynomial_equation K n hn p q h a hn₂ i z)
  simpa [nodeEvaluation, NodeDenominatorEqualizer.evalLeft] using he

/-- Inverting the actual target node coordinate retains the split origin. -/
lemma nodeEvaluation_refinement_isUnit :
    IsUnit (nodeEvaluation K n hn p q h a hn₂ i z
      (chartAlgMap K n hn p q h a hn₂ i z (sourceCoordinate K n i 0))) := by
  exact IsUnit.of_mul_eq_one _ (nodeEvaluation_coordinate K n hn p q h a hn₂ i z)

end FLT.Mazur.PolygonSplitCubicCoordinates
