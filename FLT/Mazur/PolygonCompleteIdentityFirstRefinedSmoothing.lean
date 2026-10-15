/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstCompleteSmoothing
public import FLT.Mazur.PolygonCompleteIdentityAdicRefinedKernel

/-!
# Exact second-order remainders of the original complete coordinate lifts

On refined patches, the actual source and target smoothing identities have
remainders divisible by the square of the complete parameter. This replaces
the previously unidentified open-restriction kernel by its literal generator.
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
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
local notation "W" => completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U
local notation "p" => completeIdentityAdicAmbientPatchMap K n h 1 0 0 U
local notation "ρ" => completeIdentityFirstAmbientRestriction K n h (V)
local notation "t" => parameter K 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "a" => stageCoefficientMap (C : K →+* K[T;T⁻¹]) 1
local notation "b" => ringMap (a) (t) (e) (stageCoefficientMap_parameter _ _)
local notation "σ" => reciprocalScale (e) (parameterUnit K)
local notation "x" => leftCoordinate (t)
local notation "y" => rightCoordinate (t)
local notation "s" => completeIdentityFirstCompleteSource K n h U
local notation "q" => completeIdentityFirstCompleteTarget K n h U
local notation "D" => completeIdentityFirstCompleteError K n h U
local notation "τ" => AffinePrincipalKernel.restriction (W)
  (completeIdentityActionAmbientParameter K n h)

variable (hU : (completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U).1 ≤
  completeIdentityAdicNodeNeighborhood K n h 1 0 0)
include hU

/-- The complete target smoothing remainder is divisible by the actual parameter square. -/
theorem completeIdentityFirstRefinedTarget_smoothing :
    (τ) ^ 2 ∣ (q) (x) * (q) (y) - (τ) := by
  apply (completeIdentityAdicRefinedPatch_equation_iff K n h 1 0 0 U hU _).mp
  exact completeIdentityFirstCompleteTarget_smoothing K n h U

/-- The scaled source smoothing remainder has the same exact second-order divisibility. -/
theorem completeIdentityFirstRefinedSource_smoothing :
    (τ) ^ 2 ∣ (s) ((σ) ((b) (x))) * (s) ((σ) ((b) (y))) - (τ) := by
  apply (completeIdentityAdicRefinedPatch_equation_iff K n h 1 0 0 U hU _).mp
  exact completeIdentityFirstCompleteSource_smoothing K n h U

/-- The original quadratic error expression has a complete second-order remainder. -/
theorem completeIdentityFirstRefinedError_smoothing :
    (τ) ^ 2 ∣ (s) ((σ) ((b) (x))) * (D) (y) +
      (s) ((σ) ((b) (y))) * (D) (x) + (D) (x) * (D) (y) := by
  apply (completeIdentityAdicRefinedPatch_equation_iff K n h 1 0 0 U hU _).mp
  exact completeIdentityFirstCompleteError_smoothing K n h U

/-- The previously chosen parameter lift agrees to second order with the original parameter. -/
theorem completeIdentityFirstRefinedParameter_sub :
    (τ) ^ 2 ∣ completeIdentityFirstCompleteParameter K n h U - (τ) := by
  apply (completeIdentityAdicRefinedPatch_equation_iff K n h 1 0 0 U hU _).mp
  exact completeIdentityFirstCompleteParameter_sub_mem K n h U

end FLT.Mazur.PolygonInfinitesimalStages
