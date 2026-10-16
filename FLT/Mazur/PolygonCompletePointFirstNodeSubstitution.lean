/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointNodeNumerators
public import FLT.Mazur.PolygonSmoothingScaledNodeFractions
public import FLT.Mazur.LaurentFirstStageParameter

/-!
# The same particular pole numerators under the original first-stage parameter

Both retained pole functions and their Laurent substitutions share the same
original numerator polynomials. The substitution changes every term and the
explicit denominator, while leaving the full first-stage coefficient ring intact.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentFirstStageParameter
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (i j : Fin n)
local notation "t" => parameter K 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "a" => stageCoefficientMap (C : K →+* K[T;T⁻¹]) 1
local notation "F" => scaledNodeRingMap (a) (t) (e)
  (stageCoefficientMap_parameter _ _) (parameterUnit K)
local notation "A" => ScaledNodeLocalization (a) (t) (e)
  (stageCoefficientMap_parameter _ _) (parameterUnit K)
local notation "L" => scaledNodeLocalizationMap (a) (t) (e)
  (stageCoefficientMap_parameter _ _) (parameterUnit K)
local notation "d" => nodeMarkingDenominator (t)
local notation "D" => algebraMap (ChartRing (e)) (A) ((F) (d))
local notation "P" => nodeLocalizedPolynomialMap (t)
local notation "Q" p => algebraMap (ChartRing (e)) (A)
  (Ideal.Quotient.mk (relationIdeal (e)) (scaledNodePolynomialMap (a) (parameterUnit K) p))
local notation "v" => completePointNodeLocalizedPoleTwo K n h 1 i j
local notation "w" => completePointNodeLocalizedPoleThree K n h 1 i j

/-- The same chosen original numerators control both retained poles and their full substitutions. -/
theorem completePointFirstNodePoleSubstitution_numerators :
    ∃ (r : ℕ) (p q : MvPolynomial (Fin 2) (Ring K 1)),
      (v) * algebraMap (ChartRing (t)) (StageNodeLocalization K 1) (d) ^ r = (P) p ∧
        (w) * algebraMap (ChartRing (t)) (StageNodeLocalization K 1) (d) ^ r = (P) q ∧
        (L) (v) * (D) ^ r = (Q p) ∧ (L) (w) * (D) ^ r = (Q q) := by
  obtain ⟨r, p, q, hp, hq⟩ := completePointNodePoleNumerators_exist K n h 1 i j
  exact ⟨r, p, q, hp, hq,
    scaledNodeLocalizationMap_numerator (a) (t) (e)
      (stageCoefficientMap_parameter _ _) (parameterUnit K) _ r p hp,
    scaledNodeLocalizationMap_numerator (a) (t) (e)
      (stageCoefficientMap_parameter _ _) (parameterUnit K) _ r q hq⟩

end FLT.Mazur.PolygonInfinitesimalStages
