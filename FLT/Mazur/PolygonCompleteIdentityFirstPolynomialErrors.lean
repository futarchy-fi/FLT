/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BivariateCoordinateDifference
public import FLT.Mazur.PolygonCompleteIdentityFirstNodePolynomials

/-!
# Explicit original node-error coefficients for every ambient polynomial

Substituting reciprocal-scaled source coordinates into a node polynomial
has an exact error with computable finite-sum coefficients of dx and dy.
The identity is in the full ambient ring, before any graph or fiber quotient.
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
local notation "b" => ringMap (a) (t) (e) (stageCoefficientMap_parameter _ _)
local notation "σ" => reciprocalScale (e) (parameterUnit K)
local notation "x" => leftCoordinate (t)
local notation "y" => rightCoordinate (t)
local notation "D" => completeIdentityFirstAmbientError K n h
local notation "P" => completeIdentityFirstNodePolynomialMap K n h

/-- Substitute the actual reciprocal-scaled source coordinates, inside the original source ring. -/
def completeIdentityFirstNodeScaledPolynomialMap : MvPolynomial (Fin 2) (B) →+* (B) :=
  MvPolynomial.eval₂Hom (RingHom.id (B)) ![(σ) ((b) (x)), (σ) ((b) (y))]
local notation "S" => completeIdentityFirstNodeScaledPolynomialMap K

/-- The substituted polynomial retains the literal original source-function map. -/
theorem completeIdentityFirstNodeScaledPolynomialMap_source (p : MvPolynomial (Fin 2) (B)) :
    (s) ((S) p) = MvPolynomial.eval₂Hom (s)
      ![(s) ((σ) ((b) (x))), (s) ((σ) ((b) (y)))] p := by
  rw [completeIdentityFirstNodeScaledPolynomialMap, MvPolynomial.map_eval₂Hom]
  simp only [RingHom.comp_id]
  congr 2
  funext j
  fin_cases j <;> rfl

/-- Every original polynomial error has explicit coefficients of the two actual node errors. -/
theorem completeIdentityFirstNodePolynomialMap_error (p : MvPolynomial (Fin 2) (B)) :
    (P) p - (s) ((S) p) =
      leftCoefficient (s) p ![(q) (x), (q) (y)]
          ![(s) ((σ) ((b) (x))), (s) ((σ) ((b) (y)))] * (D) (x) +
        rightCoefficient (s) p ![(q) (x), (q) (y)]
          ![(s) ((σ) ((b) (x))), (s) ((σ) ((b) (y)))] * (D) (y) := by
  rw [completeIdentityFirstNodeScaledPolynomialMap_source]
  exact evaluation_sub (s) p ![(q) (x), (q) (y)]
    ![(s) ((σ) ((b) (x))), (s) ((σ) ((b) (y)))]

end FLT.Mazur.PolygonInfinitesimalStages
