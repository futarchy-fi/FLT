/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstPoleGlobalReduction
public import FLT.Mazur.PolygonCompleteIdentityFirstPolePatchCancellation

/-!
# Original outgoing node certificates on every common pole patch

The direct cubic comparison removes affine Z compatibility from exact
ideal membership. Arbitrary ideals and nilpotents are retained throughout.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
local notation "t" => parameter K 1
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "Z" => CompleteIdentityFirstPolePatch K n h U
local notation "ρ" => completeIdentityFirstAmbientRestriction K n h (V)
local notation "ι" => algebraMap Γ((R), (V).1) (Z)
local notation "τ" => (ι) ((ρ) (completeIdentityFirstAmbientParameter K n h))
local notation "Q" => completeIdentityFirstPoleTargetMap K n h U
local notation "S" => completeIdentityFirstPoleSourceMap K n h U
local notation "η" => algebraMap (ChartRing (t)) (StageNodeLocalization K 1)
local notation "x" => (η) (leftCoordinate (t))
local notation "c" => completeIdentityFirstPoleSecantCoefficient K n h U
local notation "dx" => completeIdentityFirstAmbientError K n h (leftCoordinate (t))

local notation "E" => completePointWeierstrassCurve K n h (0 : Fin n)
local notation "F" => completePointNodeCubicFunctions K n h 1 0 0
local notation "f₂" => completePointNodeLocalizedPoleTwo K n h 1 (0 : Fin n) 0
local notation "f₃" => completePointNodeLocalizedPoleThree K n h 1 (0 : Fin n) 0

/-- Cubic differences lie in each original parameter ideal on every common patch. -/
theorem completeIdentityFirstPoleDifference_mem_everyPatch (I : Ideal (Z)) (hI : (τ) ∈ I)
    (z : WeierstrassIntegralChart.Coordinate (E) 2) : (Q) ((F) z) - (S) ((F) z) ∈ I := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [(Ideal.Quotient.mk I).map_sub, sub_eq_zero]
  exact (completeIdentityFirstPoleFunctions_eq_everyPatch K n h U
    (Ideal.Quotient.mk I) (Ideal.Quotient.eq_zero_iff_mem.mpr hI) z).symm

/-- Both retained poles satisfy exact ideal membership without patch compatibility. -/
theorem completeIdentityFirstPoleDifferences_mem_everyPatch (I : Ideal (Z)) (hI : (τ) ∈ I) :
    (Q) (f₂) - (S) (f₂) ∈ I ∧ (Q) (f₃) - (S) (f₃) ∈ I := by
  constructor
  · simpa only [completePointNodeCubicFunctions_coordinate, Matrix.cons_val_zero] using
      completeIdentityFirstPoleDifference_mem_everyPatch K n h U I hI
        (WeierstrassIntegralChart.coord (E) 2 0)
  · simpa only [completePointNodeCubicFunctions_coordinate, Matrix.cons_val_one,
      Matrix.cons_val_zero] using
      completeIdentityFirstPoleDifference_mem_everyPatch K n h U I hI
        (WeierstrassIntegralChart.coord (E) 2 1)

/-- No further localization is needed for ideals containing the original source coordinate. -/
theorem completeIdentityFirstPoleNode_error_mem_everyPatch (I : Ideal (Z))
    (ht : (τ) ∈ I) (hx : (S) (x) ∈ I) : (ι) ((ρ) (dx)) ∈ I := by
  obtain ⟨h₂, h₃⟩ := completeIdentityFirstPoleDifferences_mem_everyPatch K n h U I ht
  have hm : (c) * ((Q) (x) - (S) (x)) ∈ I := by
    rw [completeIdentityFirstPolePatch_error_equation]
    apply I.mul_mem_left
    exact I.sub_mem (I.mul_mem_left _ h₃) (I.mul_mem_left _ h₂)
  let f := Ideal.Quotient.mk I
  have hu := completeIdentityFirstPolePatch_coefficient_node_isUnit K n h U f
    (Ideal.Quotient.eq_zero_iff_mem.mpr hx)
  have he := Ideal.Quotient.eq_zero_iff_mem.mpr hm
  rw [f.map_mul] at he
  rw [← completeIdentityFirstPolePatch_error]
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  exact hu.mul_left_cancel (he.trans (mul_zero _).symm)

/-- The actual outgoing target also belongs to each such full node ideal. -/
theorem completeIdentityFirstPoleNode_target_mem_everyPatch (I : Ideal (Z))
    (ht : (τ) ∈ I) (hx : (S) (x) ∈ I) : (Q) (x) ∈ I := by
  have he := completeIdentityFirstPoleNode_error_mem_everyPatch K n h U I ht hx
  rw [← completeIdentityFirstPolePatch_error] at he
  simpa only [sub_add_cancel] using I.add_mem he hx

end FLT.Mazur.PolygonInfinitesimalStages
