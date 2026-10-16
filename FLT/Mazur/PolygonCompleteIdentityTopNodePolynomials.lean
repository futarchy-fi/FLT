/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NodeRelationPolynomialPresentation
public import FLT.Mazur.PolygonCompleteIdentityTopChartAmbientGenerators
public import FLT.Mazur.PolygonCompleteIdentityTopAmbientScalars

/-!
# Polynomial presentation of the unchanged higher node-pair relation

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
  completeIdentityTopActionUnit completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "A" => Ring K (m + 1)
local notation "t" => parameter K (m + 1)
local notation "S" => Ring K[T;T⁻¹] (m + 1)
local notation "e" => parameter K[T;T⁻¹] (m + 1)
local notation "B" => ChartRing (e)
local notation "R" => completeIdentityActionAdicChartSpace K n h (m + 1) 0 0
local notation "s" => completeIdentityTopAmbientSourceFunctions K n h m
local notation "q" => completeIdentityTopAmbientTargetFunctions K n h m
local notation "c" => RingHom.comp (algebraMap (S) (B))
  (stageCoefficientMap (C : K →+* K[T;T⁻¹]) (m + 1))

/-- Polynomials in the actual target coordinates with unchanged source-node coefficients. -/
def completeIdentityTopNodePolynomialMap : MvPolynomial (Fin 2) (B) →+* Γ((R), ⊤) :=
  nodeRelationPolynomialMap (t) (s) (q)
local notation "P" => completeIdentityTopNodePolynomialMap K n h m

/-- The two actual node maps have exactly the same truncated base coefficients. -/
theorem completeIdentityTopNodePolynomialMap_coefficients (a : A) :
    (s) ((c) a) = (q) (algebraMap (A) (ChartRing (t)) a) := by
  rw [completeIdentityTopAmbientTarget_scalar]
  exact completeIdentityTopAmbientSource_scalar K n h m a

/-- Every full ambient function is a polynomial in the original node variables. -/
theorem completeIdentityTopNodePolynomialMap_surjective : Function.Surjective (P) :=
  nodeRelationPolynomialMap_surjective (t) (s) (q) (c)
    (completeIdentityTopNodePolynomialMap_coefficients K n h m)
    (completeIdentityTopAmbientFunctions_generate K n h m)

/-- Constants retain the original source map, including the full Laurent parameter. -/
theorem completeIdentityTopNodePolynomialMap_constant (b : B) :
    (P) (MvPolynomial.C b) = (s) b := MvPolynomial.eval₂_C _ _ _

/-- The first polynomial variable is the unchanged original target coordinate. -/
theorem completeIdentityTopNodePolynomialMap_left :
    (P) (MvPolynomial.X 0) = (q) (leftCoordinate (t)) :=
  MvPolynomial.eval₂_X _ _ _

/-- The second polynomial variable is the unchanged original reciprocal target coordinate. -/
theorem completeIdentityTopNodePolynomialMap_right :
    (P) (MvPolynomial.X 1) = (q) (rightCoordinate (t)) :=
  MvPolynomial.eval₂_X _ _ _

end FLT.Mazur.PolygonInfinitesimalStages
