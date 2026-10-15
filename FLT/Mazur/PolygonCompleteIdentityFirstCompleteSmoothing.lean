/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAmbientErrorRelation
public import FLT.Mazur.PolygonCompleteIdentityFirstParameterEquations

/-!
# Original smoothing equations for the complete coordinate representatives

The lifted source, target and errors obey the actual original smoothing
identities modulo the adic ambient kernel. The graph ideal is not imposed.
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

/-- The two lifted target coordinates multiply to the actual parameter modulo adic equations. -/
theorem completeIdentityFirstCompleteTarget_smoothing :
    (q) (x) * (q) (y) - (τ) ∈ RingHom.ker (p).hom := by
  change (p) (_ - _) = 0
  rw [map_sub, map_mul, completeIdentityFirstCompleteTarget_spec,
    completeIdentityFirstCompleteTarget_spec, ← map_mul,
    completeIdentityFirstAmbientTarget_xy, completeIdentityActionAmbientParameter_patch,
    sub_self]

/-- The lifted scaled-source coordinates obey the same actual parameter equation. -/
theorem completeIdentityFirstCompleteSource_smoothing :
    (s) ((σ) ((b) (x))) * (s) ((σ) ((b) (y))) - (τ) ∈ RingHom.ker (p).hom := by
  change (p) (_ - _) = 0
  rw [map_sub, map_mul, completeIdentityFirstCompleteSource_spec,
    completeIdentityFirstCompleteSource_spec, ← map_mul,
    completeIdentityFirstAmbientScaledSource_xy, completeIdentityActionAmbientParameter_patch,
    sub_self]

/-- The complete original errors satisfy the quadratic relation modulo the full adic kernel. -/
theorem completeIdentityFirstCompleteError_smoothing :
    (s) ((σ) ((b) (x))) * (D) (y) + (s) ((σ) ((b) (y))) * (D) (x) +
      (D) (x) * (D) (y) ∈ RingHom.ker (p).hom := by
  change (p) _ = 0
  simp only [map_add, map_mul, completeIdentityFirstCompleteSource_spec,
    completeIdentityFirstCompleteError_spec]
  rw [← map_mul, ← map_mul, ← map_mul, ← map_add, ← map_add,
    completeIdentityFirstAmbientError_smoothing, map_zero]

end FLT.Mazur.PolygonInfinitesimalStages
