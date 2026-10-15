/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstChartAmbientTarget

/-!
# Original ambient target errors in the full closed fiber

Every target-minus-scaled-source function lies in the full residual node
kernel. These are actual functions before and after imposing the graph
ideal; no error or residual ideal is asserted to vanish.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentFirstStageParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "t" => parameter K 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "B" => ChartRing (t)
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "a" => stageCoefficientMap (C : K →+* K[T;T⁻¹]) 1
local notation "b" => ringMap (a) (t) (e) (stageCoefficientMap_parameter _ _)
local notation "σ" => reciprocalScale (e) (parameterUnit K)
local notation "s" => completeIdentityFirstAmbientSourceFunctions K n h
local notation "p" => completeIdentityFirstAmbientTargetFunctions K n h
local notation "f" => completeIdentityFirstChartClosedAmbientMap K n h
local notation "d" => completeIdentityFirstAmbientNodeReduction K n h
local notation "r" => completeIdentityFirstChartClosedReduction K n h
local notation "q" => completeIdentityFirstChartClosedQuotient K n h

/-- The actual target error in the original ambient node-relation ring. -/
def completeIdentityFirstAmbientError (z : B) : Γ((R), ⊤) := (p) z - (s) ((σ) ((b) z))

/-- The original node reduction kills each full ambient target error. -/
theorem completeIdentityFirstAmbientError_reduction (z : B) :
    (d) (completeIdentityFirstAmbientError K n h z) = 0 := by
  rw [completeIdentityFirstAmbientError, map_sub,
    completeIdentityFirstAmbientNodeReduction_target,
    completeIdentityFirstAmbientNodeReduction_source, sub_self]

/-- The full closed-fiber error retains the original ambient representative. -/
def completeIdentityFirstChartClosedError (z : B) :
    completeIdentityFirstChartClosedFiber K n h :=
  (f) (completeIdentityFirstAmbientError K n h z)

/-- The closed error is precisely the actual target minus the actual scaled source. -/
theorem completeIdentityFirstChartClosedError_eq (z : B) :
    completeIdentityFirstChartClosedError K n h z =
      (q) (completeIdentityFirstChartTargetFunctions K n h z) -
        (q) (completeIdentityFirstChartSourceFunctions K n h ((σ) ((b) z))) := by
  change (q) ((completeIdentityActionGraphAdicChartEmbedding K n h 1 0 0).appTop
    ((p) z - (s) ((σ) ((b) z)))) = _
  rw [map_sub, completeIdentityFirstAmbientTargetFunctions_restrict,
    completeIdentityFirstAmbientSourceFunctions_restrict, map_sub]

/-- Every actual closed error belongs to the full residual node-retraction kernel. -/
theorem completeIdentityFirstChartClosedError_mem (z : B) :
    completeIdentityFirstChartClosedError K n h z ∈ RingHom.ker (r) :=
  completeIdentityFirstAmbientError_reduction K n h z

/-- Error vanishing means membership in the original graph-plus-parameter ideal. -/
theorem completeIdentityFirstChartClosedError_eq_zero_iff (z : B) :
    completeIdentityFirstChartClosedError K n h z = 0 ↔
      completeIdentityFirstAmbientError K n h z ∈
        completeIdentityFirstChartClosedAmbientIdeal K n h :=
  completeIdentityFirstChartClosedAmbientMap_eq_zero K n h _

end FLT.Mazur.PolygonInfinitesimalStages
