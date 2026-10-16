/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstNodePolynomials
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Four original node variables over the unchanged Laurent coefficient ring

Unpack the source node coefficients as polynomials as well. The resulting
surjective map has precisely the two target and the two source variables.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "S" => Ring K[T;T⁻¹] 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "t" => parameter K 1
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "P" => completeIdentityFirstNodePolynomialMap K n h
local notation "s" => completeIdentityFirstAmbientSourceFunctions K n h
local notation "q" => completeIdentityFirstAmbientTargetFunctions K n h

/-- The actual four-variable presentation, with the original Laurent coefficient ring. -/
def completeIdentityFirstFourCoordinateMap :
    MvPolynomial (Fin 2 ⊕ Fin 2) (S) →+* Γ((R), ⊤) :=
  (P).comp ((MvPolynomial.map (Ideal.Quotient.mk (relationIdeal (e)))).comp
    (MvPolynomial.sumRingEquiv (S) (Fin 2) (Fin 2)).toRingHom)
local notation "F" => completeIdentityFirstFourCoordinateMap K n h

/-- No full ambient functions are lost by using these four original node variables. -/
theorem completeIdentityFirstFourCoordinateMap_surjective : Function.Surjective (F) :=
  (completeIdentityFirstNodePolynomialMap_surjective K n h).comp
    ((MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective).comp
      (MvPolynomial.sumRingEquiv (S) (Fin 2) (Fin 2)).surjective)

/-- The first target variable is the original target x coordinate. -/
theorem completeIdentityFirstFourCoordinateMap_target_left :
    (F) (MvPolynomial.X (.inl 0)) = (q) (leftCoordinate (t)) := by
  simp [completeIdentityFirstFourCoordinateMap, completeIdentityFirstNodePolynomialMap_left]

/-- The second target variable is the original target y coordinate. -/
theorem completeIdentityFirstFourCoordinateMap_target_right :
    (F) (MvPolynomial.X (.inl 1)) = (q) (rightCoordinate (t)) := by
  simp [completeIdentityFirstFourCoordinateMap, completeIdentityFirstNodePolynomialMap_right]

/-- The first source variable retains its actual original source map. -/
theorem completeIdentityFirstFourCoordinateMap_source_left :
    (F) (MvPolynomial.X (.inr 0)) = (s) (leftCoordinate (e)) := by
  simp [completeIdentityFirstFourCoordinateMap, completeIdentityFirstNodePolynomialMap_constant,
    leftCoordinate]

/-- The reciprocal source variable also retains the original source map. -/
theorem completeIdentityFirstFourCoordinateMap_source_right :
    (F) (MvPolynomial.X (.inr 1)) = (s) (rightCoordinate (e)) := by
  simp [completeIdentityFirstFourCoordinateMap, completeIdentityFirstNodePolynomialMap_constant,
    rightCoordinate]

end FLT.Mazur.PolygonInfinitesimalStages
