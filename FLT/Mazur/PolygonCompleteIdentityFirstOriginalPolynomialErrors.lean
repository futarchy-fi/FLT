/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingScaledNodePolynomials
public import FLT.Mazur.PolygonCompleteIdentityFirstPolynomialErrors

/-!
# Finite error coefficients for the original node polynomial numerators

Original two-variable numerators feed directly into the full ambient error
formula. The Laurent action parameter and every lower coefficient are retained.
The explicit denominator error is computed without asserting it vanishes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentFirstStageParameter
open BivariateCoordinateDifference
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "t" => parameter K 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "B" => ChartRing (e)
local notation "s" => completeIdentityFirstAmbientSourceFunctions K n h
local notation "q" => completeIdentityFirstAmbientTargetFunctions K n h
local notation "a" => stageCoefficientMap (C : K →+* K[T;T⁻¹]) 1
local notation "c" => RingHom.comp (algebraMap (Ring K[T;T⁻¹] 1) (B)) (a)
local notation "F" => scaledNodeRingMap (a) (t) (e)
  (stageCoefficientMap_parameter _ _) (parameterUnit K)
local notation "x" => leftCoordinate (t)
local notation "y" => rightCoordinate (t)
local notation "X" => ![(q) (x), (q) (y)]
local notation "Y" => ![(s) ((F) (x)), (s) ((F) (y))]

/-- Actual target evaluation of the original node polynomial, before any graph quotient. -/
theorem completeIdentityFirstOriginalPolynomial_target
    (p : MvPolynomial (Fin 2) (Ring K 1)) :
    completeIdentityFirstNodePolynomialMap K n h (MvPolynomial.map (c) p) =
      (q) (Ideal.Quotient.mk (relationIdeal (t)) p) :=
  nodeRelationPolynomialMap_target (t) (s) (q) (c)
    (completeIdentityFirstNodePolynomialMap_coefficients K n h) p

omit n h [NeZero n] in
/-- The original parameter acts by literal substitution on all polynomial coefficients. -/
theorem completeIdentityFirstOriginalPolynomial_scaled
    (p : MvPolynomial (Fin 2) (Ring K 1)) :
    completeIdentityFirstNodeScaledPolynomialMap K (MvPolynomial.map (c) p) =
      (F) (Ideal.Quotient.mk (relationIdeal (t)) p) := by
  apply nodeRelationPolynomialMap_target (t) (RingHom.id (B)) (F) (c) _ p
  intro z
  simp only [RingHom.id_apply, RingHom.comp_apply, scaledNodeRingMap,
    ringMap_scalar, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]

/-- The original polynomial error has the existing explicit finite-sum coordinate coefficients. -/
theorem completeIdentityFirstOriginalPolynomial_error
    (p : MvPolynomial (Fin 2) (Ring K 1)) :
    (q) (Ideal.Quotient.mk (relationIdeal (t)) p) -
        (s) ((F) (Ideal.Quotient.mk (relationIdeal (t)) p)) =
      leftCoefficient (s) (MvPolynomial.map (c) p) (X) (Y) *
          completeIdentityFirstAmbientError K n h (x) +
        rightCoefficient (s) (MvPolynomial.map (c) p) (X) (Y) *
          completeIdentityFirstAmbientError K n h (y) := by
  rw [← completeIdentityFirstOriginalPolynomial_target,
    ← completeIdentityFirstOriginalPolynomial_scaled]
  exact completeIdentityFirstNodePolynomialMap_error K n h _

/-- The explicit denominator's complete ambient error retains both original coordinate errors. -/
theorem completeIdentityFirstNodeDenominator_error :
    (q) (nodeMarkingDenominator (t)) - (s) ((F) (nodeMarkingDenominator (t))) =
      ((q) (y) - 1) * completeIdentityFirstAmbientError K n h (x) +
        ((s) ((F) (x)) - 1) * completeIdentityFirstAmbientError K n h (y) := by
  simp only [nodeMarkingDenominator, map_mul, RingHom.map_sub, map_one]
  change (1 - (q) (x)) * (1 - (q) (y)) -
      (1 - (s) ((F) (x))) * (1 - (s) ((F) (y))) =
    ((q) (y) - 1) * ((q) (x) - (s) ((F) (x))) +
      ((s) ((F) (x)) - 1) * ((q) (y) - (s) ((F) (y)))
  ring

end FLT.Mazur.PolygonInfinitesimalStages
