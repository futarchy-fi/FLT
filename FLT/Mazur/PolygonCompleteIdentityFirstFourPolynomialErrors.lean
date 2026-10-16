/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstPolynomialConversion

/-!
# Explicit errors of original four-coordinate polynomials

The conversion groups source variables into coefficients. Finite polynomial
sums then compute the coefficients of the two original target errors, without
passing to a reduced fiber or changing the original Laurent parameter.
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
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "S" => Ring K[T;T⁻¹] 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "t" => parameter K 1
local notation "s" => completeIdentityFirstAmbientSourceFunctions K n h
local notation "q" => completeIdentityFirstAmbientTargetFunctions K n h
local notation "a" => stageCoefficientMap (C : K →+* K[T;T⁻¹]) 1
local notation "b" => ringMap (a) (t) (e) (stageCoefficientMap_parameter _ _)
local notation "σ" => reciprocalScale (e) (parameterUnit K)
local notation "x" => leftCoordinate (t)
local notation "y" => rightCoordinate (t)
local notation "X" => ![(q) (x), (q) (y)]
local notation "Y" => ![(s) ((σ) ((b) (x))), (s) ((σ) ((b) (y)))]
local notation "C₄" => completeIdentityFirstPolynomialConversion K

/-- Substitute scaled source coordinates into the actual four-variable polynomial. -/
def completeIdentityFirstFourScaledMap :
    MvPolynomial (Fin 2 ⊕ Fin 2) (S) →+* ChartRing (e) :=
  (completeIdentityFirstNodeScaledPolynomialMap K).comp (C₄)

/-- Explicit finite-sum coefficient of the original x error. -/
def completeIdentityFirstFourLeftCoefficient
    (p : MvPolynomial (Fin 2 ⊕ Fin 2) (S)) : Γ((R), ⊤) :=
  leftCoefficient (s) ((C₄) p) (X) (Y)

/-- Explicit finite-sum coefficient of the original y error. -/
def completeIdentityFirstFourRightCoefficient
    (p : MvPolynomial (Fin 2 ⊕ Fin 2) (S)) : Γ((R), ⊤) :=
  rightCoefficient (s) ((C₄) p) (X) (Y)

/-- The exact full-ring polynomial error retains its two computed coordinate coefficients. -/
theorem completeIdentityFirstFourPolynomial_error
    (p : MvPolynomial (Fin 2 ⊕ Fin 2) (S)) :
    completeIdentityFirstFourCoordinateMap K n h p -
        (s) (completeIdentityFirstFourScaledMap K p) =
      completeIdentityFirstFourLeftCoefficient K n h p *
          completeIdentityFirstAmbientError K n h (x) +
        completeIdentityFirstFourRightCoefficient K n h p *
          completeIdentityFirstAmbientError K n h (y) :=
  completeIdentityFirstNodePolynomialMap_error K n h ((C₄) p)

end FLT.Mazur.PolygonInfinitesimalStages
