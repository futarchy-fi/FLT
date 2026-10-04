/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSplitRefinementCover

/-!
# All interpolation coordinates at a split node

Clear the Laurent denominator on the normalization before evaluating its
origin. The values retain both component indices, including for the two-gon.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open scoped LaurentPolynomial
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonSplitCubicCoordinates
open PolygonPinching PolygonNodeAffineCharts PolygonNodeEqualizer PolygonNodeLocalization
open PolygonNodePresentation PolygonCubicSections PolygonPowerNodeEndpoints
open LocalizationJointRestriction
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ) (hn₂ : 2 ≤ n) (i : Fin n) (z : Spec (.of K))

/-- The unpunctured polynomial numerator for any interpolation coordinate. -/
def leftNumerator (l : Fin n) (k : Fin 3) : K[X] :=
  Polynomial.C (cubicDelta K n l k 0 i) +
    Polynomial.C (cubicDelta K n l k 1 i) * X +
    Polynomial.C (cubicDelta K n l k 2 i) * X ^ 2 +
    Polynomial.C (weight K n a 3 i * cubicDelta K n l k 0 ((finRotate n).symm i)) * X ^ 3

omit [NeZero n] in
/-- Dividing this polynomial by T gives the previously computed Laurent numerator. -/
lemma leftNumerator_laurent (l : Fin n) (k : Fin 3) :
    (leftNumerator K n a i l k).toLaurent * LaurentPolynomial.T (-1) =
      interpolationLaurent K n a i l k := by
  simp only [leftNumerator, map_add, map_mul, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X, Polynomial.toLaurent_X_pow, add_mul, mul_assoc,
    ← LaurentPolynomial.T_add, interpolationLaurent]
  simp

local notation "s" => splitDenominator K n hn p q h a hn₂ i z
local notation "c" => coordinate K n hn p q h a hn₂ i z

/-- Every interpolation ratio satisfies its polynomial equation before puncturing. -/
lemma left_interpolation_polynomial_equation (l : Fin n) (k : Fin 3) :
    NodeDenominatorRestriction.left s (c l k) *
      algebraMap K[X] (Localization.Away (first s)) ((X - Polynomial.C (a i : K)) ^ 3) =
        algebraMap K[X] (Localization.Away (first s)) (leftNumerator K n a i l k) := by
  apply restriction_injective (Polynomial.toLaurent : K[X] →+* LaurentPolynomial K)
    (first s) Polynomial.toLaurent_injective
  rw [map_mul, restriction_algebraMap, restriction_algebraMap]
  change NodePuncturedDenominatorRestriction.left s (c l k) *
    algebraMap (LaurentPolynomial K) (Localization.Away (first s).toLaurent)
      (Polynomial.toLaurent ((X - Polynomial.C (a i : K)) ^ 3)) = _
  have he := split_left_interpolation_equation K n hn p q h a hn₂ i z l k
  dsimp only at he
  rw [← leftNumerator_laurent, PuncturedNodeRestrictionComparison.left_eq] at he
  change NodePuncturedDenominatorRestriction.left s (c l k) *
    algebraMap (LaurentPolynomial K) (Localization.Away (first s).toLaurent)
      ((LaurentPolynomial.T 1 - LaurentPolynomial.C (a i : K)) ^ 3 *
        LaurentPolynomial.T (-1)) =
      algebraMap (LaurentPolynomial K) (Localization.Away (first s).toLaurent)
        ((leftNumerator K n a i l k).toLaurent * LaurentPolynomial.T (-1)) at he
  have ht : IsUnit (algebraMap (LaurentPolynomial K) (Localization.Away (first s).toLaurent)
      (LaurentPolynomial.T (-1))) := (LaurentPolynomial.isUnit_T (-1)).map _
  apply ht.mul_right_cancel
  rw [mul_assoc, ← map_mul, ← map_mul]
  simpa only [map_pow, map_sub, Polynomial.toLaurent_X, Polynomial.toLaurent_C] using he

/-- The node value of each coordinate is its prescribed constant coefficient. -/
lemma nodeEvaluation_interpolation (l : Fin n) (k : Fin 3) :
    nodeEvaluation K n hn p q h a hn₂ i z (c l k) * (-(a i : K)) ^ 3 =
      cubicDelta K n l k 0 i := by
  have he := congrArg (NodeDenominatorEqualizer.evalLeft s
    (splitDenominator_value_isUnit K n hn p q h a hn₂ i z))
      (left_interpolation_polynomial_equation K n hn p q h a hn₂ i z l k)
  simpa [nodeEvaluation, NodeDenominatorEqualizer.evalLeft, leftNumerator] using he

/-- Every branch-linear coordinate vanishes at every split node. -/
lemma nodeEvaluation_linear (l : Fin n) :
    nodeEvaluation K n hn p q h a hn₂ i z (c l 1) = 0 := by
  have he := nodeEvaluation_interpolation K n hn p q h a hn₂ i z l 1
  simp only [cubicDelta, show (0 : Fin 3) ≠ 1 by decide, and_false, ite_false] at he
  exact (mul_eq_zero.mp he).resolve_right (pow_ne_zero _ (neg_ne_zero.mpr (a i).ne_zero))

/-- The node-value coordinate is nonzero precisely at its own node. -/
lemma nodeEvaluation_node_ne_zero_iff (l : Fin n) :
    nodeEvaluation K n hn p q h a hn₂ i z (c l 0) ≠ 0 ↔ i = l := by
  have he := nodeEvaluation_interpolation K n hn p q h a hn₂ i z l 0
  by_cases hil : i = l
  · subst l
    simp only [cubicDelta, and_self, ite_true] at he
    exact iff_of_true (by intro hz; rw [hz, zero_mul] at he; exact zero_ne_one he) rfl
  · simp only [cubicDelta, hil, false_and, ite_false] at he
    have hz := (mul_eq_zero.mp he).resolve_right
      (pow_ne_zero _ (neg_ne_zero.mpr (a i).ne_zero))
    simp [hz, hil]

end FLT.Mazur.PolygonSplitCubicCoordinates
