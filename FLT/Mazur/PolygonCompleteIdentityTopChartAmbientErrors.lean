/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopChartAmbientTarget

/-!
# Original ambient target errors in the full closed fiber

Each target-minus-scaled-source function is retained before and after
imposing the original graph-plus-parameter ideal. Its evaluation gives
the actual higher action defect; error vanishing remains to be proved.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentStageParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityTopActionUnit completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "t" => parameter K (m + 1)
local notation "e" => parameter K[T;T⁻¹] (m + 1)
local notation "B" => ChartRing (t)
local notation "R" => completeIdentityActionAdicChartSpace K n h (m + 1) 0 0
local notation "a" => stageCoefficientMap (C : K →+* K[T;T⁻¹]) (m + 1)
local notation "b" => ringMap (a) (t) (e) (stageCoefficientMap_parameter _ _)
local notation "σ" => reciprocalScale (e) (parameterUnit K (m + 1))
local notation "s" => completeIdentityTopAmbientSourceFunctions K n h m
local notation "p" => completeIdentityTopAmbientTargetFunctions K n h m
local notation "f" => completeIdentityTopChartClosedAmbientMap K n h m
local notation "q" => completeIdentityTopChartClosedQuotient K n h m

/-- The actual target error in the original ambient node-relation ring. -/
def completeIdentityTopAmbientError (z : B) : Γ((R), ⊤) := (p) z - (s) ((σ) ((b) z))

/-- Evaluation of the full ambient error retains the actual two-branch action defect. -/
theorem completeIdentityTopAmbientError_evaluation (z : B) :
    (SpectrumGlobalRange.ringHom (completeIdentityTopGraphToChart K n h m)
      ((completeIdentityActionGraphAdicChartEmbedding K n h (m + 1) 0 0).appTop
        (completeIdentityTopAmbientError K n h m z))).val =
      completeIdentityTopActionNodeDefect K n h 0 m ((b) z) := by
  rw [completeIdentityTopAmbientError, map_sub,
    completeIdentityTopAmbientTargetFunctions_restrict,
    completeIdentityTopAmbientSourceFunctions_restrict, map_sub,
    completeIdentityTopChartTargetFunctions_evaluation,
    completeIdentityTopChartSourceFunctions_evaluation]
  rfl

/-- The full closed-fiber error retains the original ambient representative. -/
def completeIdentityTopChartClosedError (z : B) :
    completeIdentityTopChartClosedFiber K n h m :=
  (f) (completeIdentityTopAmbientError K n h m z)

/-- The closed error is precisely the actual target minus the actual scaled source. -/
theorem completeIdentityTopChartClosedError_eq (z : B) :
    completeIdentityTopChartClosedError K n h m z =
      (q) (completeIdentityTopChartTargetFunctions K n h m z) -
        (q) (completeIdentityTopChartSourceFunctions K n h m ((σ) ((b) z))) := by
  change (q) ((completeIdentityActionGraphAdicChartEmbedding K n h (m + 1) 0 0).appTop
    ((p) z - (s) ((σ) ((b) z)))) = _
  rw [map_sub, completeIdentityTopAmbientTargetFunctions_restrict,
    completeIdentityTopAmbientSourceFunctions_restrict, map_sub]

/-- Error vanishing means membership in the original graph-plus-parameter ideal. -/
theorem completeIdentityTopChartClosedError_eq_zero_iff (z : B) :
    completeIdentityTopChartClosedError K n h m z = 0 ↔
      completeIdentityTopAmbientError K n h m z ∈
        completeIdentityTopChartClosedAmbientIdeal K n h m :=
  completeIdentityTopChartClosedAmbientMap_eq_zero K n h m _

end FLT.Mazur.PolygonInfinitesimalStages
