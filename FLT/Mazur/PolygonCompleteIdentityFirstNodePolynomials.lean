/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NodeRelationPolynomialPresentation
public import FLT.Mazur.PolygonCompleteIdentityFirstChartAmbientGenerators
public import FLT.Mazur.PolygonCompleteIdentityAmbientErrorRelation

/-!
# Polynomial presentation of the unchanged first node-pair relation

The coefficients are the original source node ring, including its Laurent
parameter. The two variables are the original target node coordinates.
Every ambient function has such an expression before imposing the graph ideal.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "A" => Ring K 1
local notation "t" => parameter K 1
local notation "S" => Ring K[T;T⁻¹] 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "B" => ChartRing (e)
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "s" => completeIdentityFirstAmbientSourceFunctions K n h
local notation "q" => completeIdentityFirstAmbientTargetFunctions K n h
local notation "c" => RingHom.comp (algebraMap (S) (B))
  (stageCoefficientMap (C : K →+* K[T;T⁻¹]) 1)

/-- Polynomials in the actual target coordinates with unchanged source-node coefficients. -/
def completeIdentityFirstNodePolynomialMap : MvPolynomial (Fin 2) (B) →+* Γ((R), ⊤) :=
  nodeRelationPolynomialMap (t) (s) (q)
local notation "P" => completeIdentityFirstNodePolynomialMap K n h

/-- The two actual node maps have exactly the same truncated base coefficients. -/
theorem completeIdentityFirstNodePolynomialMap_coefficients (a : A) :
    (s) ((c) a) = (q) (algebraMap (A) (ChartRing (t)) a) := by
  rw [completeIdentityFirstAmbientTarget_scalar]
  exact completeIdentityFirstAmbientSource_scalar K n h a

/-- Every full ambient function is a polynomial in the original node variables. -/
theorem completeIdentityFirstNodePolynomialMap_surjective : Function.Surjective (P) :=
  nodeRelationPolynomialMap_surjective (t) (s) (q) (c)
    (completeIdentityFirstNodePolynomialMap_coefficients K n h)
    (completeIdentityFirstAmbientFunctions_generate K n h)

/-- Constants retain the original source map, including the full Laurent parameter. -/
theorem completeIdentityFirstNodePolynomialMap_constant (b : B) :
    (P) (MvPolynomial.C b) = (s) b := MvPolynomial.eval₂_C _ _ _

/-- The first polynomial variable is the unchanged original target coordinate. -/
theorem completeIdentityFirstNodePolynomialMap_left :
    (P) (MvPolynomial.X 0) = (q) (leftCoordinate (t)) :=
  MvPolynomial.eval₂_X _ _ _

/-- The second polynomial variable is the unchanged original reciprocal target coordinate. -/
theorem completeIdentityFirstNodePolynomialMap_right :
    (P) (MvPolynomial.X 1) = (q) (rightCoordinate (t)) :=
  MvPolynomial.eval₂_X _ _ _

end FLT.Mazur.PolygonInfinitesimalStages
