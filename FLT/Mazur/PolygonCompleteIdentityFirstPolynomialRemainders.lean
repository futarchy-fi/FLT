/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstPolynomialErrors
public import FLT.Mazur.PolygonCompleteIdentityFirstCompleteErrors
public import FLT.Mazur.PolygonCompleteIdentityAdicRefinedKernel

/-!
# Complete polynomial error equations with exact second-order remainders

The explicit coefficients of dx and dy lift to the original complete patch.
Their error identity has a remainder divisible by the actual parameter square.
No multiplicativity of the chosen section lifts is assumed.
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
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
local notation "t" => parameter K 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "B" => ChartRing (e)
local notation "s" => completeIdentityFirstAmbientSourceFunctions K n h
local notation "q" => completeIdentityFirstAmbientTargetFunctions K n h
local notation "a" => stageCoefficientMap (C : K →+* K[T;T⁻¹]) 1
local notation "b" => ringMap (a) (t) (e) (stageCoefficientMap_parameter _ _)
local notation "σ" => reciprocalScale (e) (parameterUnit K)
local notation "x" => leftCoordinate (t)
local notation "y" => rightCoordinate (t)
local notation "X" => ![(q) (x), (q) (y)]
local notation "Y" => ![(s) ((σ) ((b) (x))), (s) ((σ) ((b) (y)))]
local notation "D" => completeIdentityFirstCompleteError K n h U
local notation "P" => completeIdentityFirstNodePolynomialMap K n h
local notation "S" => completeIdentityFirstNodeScaledPolynomialMap K
local notation "L" => completeIdentityAdicAmbientLift K n h 1 0 0 U
local notation "W" => completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U
local notation "ρ" => completeIdentityFirstAmbientRestriction K n h (V)
local notation "π" => completeIdentityAdicAmbientPatchMap K n h 1 0 0 U
local notation "τ" => AffinePrincipalKernel.restriction (W)
  (completeIdentityActionAmbientParameter K n h)

/-- The actual complete polynomial error retains its explicit original coordinate coefficients. -/
theorem completeIdentityFirstPolynomialError_remainder
    (hU : (completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U).1 ≤
      completeIdentityAdicNodeNeighborhood K n h 1 0 0)
    (p : MvPolynomial (Fin 2) (B)) :
    (τ) ^ 2 ∣ (L) ((P) p) - completeIdentityFirstCompleteSource K n h U ((S) p) -
      ((L) (leftCoefficient (s) p (X) (Y)) * (D) (x) +
        (L) (rightCoefficient (s) p (X) (Y)) * (D) (y)) := by
  apply (completeIdentityAdicRefinedPatch_equation_iff K n h 1 0 0 U hU _).mp
  simp only [map_sub, map_add, map_mul, completeIdentityAdicAmbientLift_spec,
    completeIdentityFirstCompleteSource_spec, completeIdentityFirstCompleteError_spec]
  change (ρ) ((P) p) - (ρ) ((s) ((S) p)) -
    ((ρ) (leftCoefficient (s) p (X) (Y)) *
        (ρ) (completeIdentityFirstAmbientError K n h (x)) +
      (ρ) (rightCoefficient (s) p (X) (Y)) *
        (ρ) (completeIdentityFirstAmbientError K n h (y))) = 0
  rw [← map_sub, ← map_mul, ← map_mul, ← map_add,
    completeIdentityFirstNodePolynomialMap_error, sub_self]

end FLT.Mazur.PolygonInfinitesimalStages
