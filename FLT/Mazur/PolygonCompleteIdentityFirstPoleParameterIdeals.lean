/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstPoleSourceReduction
public import FLT.Mazur.PolygonCompleteIdentityFirstPolePatchCancellation

/-!
# Actual pole differences and the original outgoing graph-error certificate

Both original pole differences belong to every ideal containing the original
parameter. The secant criterion transfers this to the original outgoing error
on its explicit neighborhood, in particular for the full graph-plus-parameter ideal.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
variable (hC : (completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U).1 ≤
  completeIdentityCubicChartOpen K n h 2)
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "Z" => CompleteIdentityFirstPolePatch K n h U
local notation "ρ" => completeIdentityFirstAmbientRestriction K n h (V)
local notation "ι" => algebraMap Γ((R), (V).1) (Z)
local notation "τ" => (ι) ((ρ) (completeIdentityFirstAmbientParameter K n h))
local notation "Q" => completeIdentityFirstPoleTargetMap K n h U
local notation "S" => completeIdentityFirstPoleSourceMap K n h U
local notation "E" => completePointWeierstrassCurve K n h (0 : Fin n)
local notation "F" => completePointNodeCubicFunctions K n h 1 0 0
local notation "f₂" => completePointNodeLocalizedPoleTwo K n h 1 (0 : Fin n) 0
local notation "f₃" => completePointNodeLocalizedPoleThree K n h 1 (0 : Fin n) 0
include hC

/-- Every actual cubic-function difference lies in each original parameter-containing ideal. -/
theorem completeIdentityFirstPoleDifference_mem (I : Ideal (Z)) (hI : (τ) ∈ I)
    (z : Coordinate (E) 2) : (Q) ((F) z) - (S) ((F) z) ∈ I := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [(Ideal.Quotient.mk I).map_sub, sub_eq_zero]
  exact (completeIdentityFirstPoleFunctions_eq_of_parameter_zero K n h U hC
    (Ideal.Quotient.mk I) (Ideal.Quotient.eq_zero_iff_mem.mpr hI) z).symm

/-- The two retained pole differences belong to the full original parameter ideal. -/
theorem completeIdentityFirstPoleDifferences_mem (I : Ideal (Z)) (hI : (τ) ∈ I) :
    (Q) (f₂) - (S) (f₂) ∈ I ∧ (Q) (f₃) - (S) (f₃) ∈ I := by
  constructor
  · simpa only [completePointNodeCubicFunctions_coordinate, Matrix.cons_val_zero] using
      completeIdentityFirstPoleDifference_mem K n h U hC I hI (coord (E) 2 0)
  · simpa only [completePointNodeCubicFunctions_coordinate, Matrix.cons_val_one,
      Matrix.cons_val_zero] using
      completeIdentityFirstPoleDifference_mem K n h U hC I hI (coord (E) 2 1)

local notation "T" => CompleteIdentityFirstPoleSecantPatch K n h U
local notation "ν" => algebraMap (Z) (T)
local notation "dx" => completeIdentityFirstAmbientError K n h (leftCoordinate (parameter K 1))

/-- The actual outgoing error vanishes modulo any parameter ideal on the secant neighborhood. -/
theorem completeIdentityFirstPoleSecant_error_mem (I : Ideal (T)) (hI : (ν) (τ) ∈ I) :
    (ν) ((ι) ((ρ) (dx))) ∈ I := by
  obtain ⟨h₂, h₃⟩ := completeIdentityFirstPoleDifferences_mem K n h U hC (I.comap (ν)) hI
  exact completeIdentityFirstPolePatch_error_mem K n h U I h₂ h₃

/-- In particular this is membership in the unchanged full graph-plus-parameter ideal. -/
theorem completeIdentityFirstPoleSecant_graphError_mem :
    (ν) ((ι) ((ρ) (dx))) ∈
      (((completeIdentityFirstChartClosedAmbientIdeal K n h).map (ρ).hom).map (ι)).map (ν) := by
  apply completeIdentityFirstPoleSecant_error_mem K n h U hC
  apply Ideal.mem_map_of_mem
  apply Ideal.mem_map_of_mem
  apply Ideal.mem_map_of_mem
  exact (show Ideal.span {completeIdentityFirstAmbientParameter K n h} ≤
    completeIdentityFirstChartClosedAmbientIdeal K n h from le_sup_right)
      (Ideal.subset_span (Set.mem_singleton _))

end FLT.Mazur.PolygonInfinitesimalStages
