/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstPolePatchNode

/-!
# Cancel the actual secant coefficient near the original source node

On the explicit principal neighborhood containing that node, the original
coordinate error belongs to every ideal containing the two retained pole
errors. No membership in the complete graph ideal is assumed or asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
local notation "t" => parameter K 1
local notation "η" => algebraMap (ChartRing (t)) (StageNodeLocalization K 1)
local notation "Q" => completeIdentityFirstPoleTargetMap K n h U
local notation "S" => completeIdentityFirstPoleSourceMap K n h U
local notation "Z" => CompleteIdentityFirstPolePatch K n h U
local notation "c" => completeIdentityFirstPoleSecantCoefficient K n h U
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "ρ" => completeIdentityFirstAmbientRestriction K n h (V)
local notation "ι" => algebraMap Γ((R), (V).1) (Z)
local notation "f₂" => completePointNodeLocalizedPoleTwo K n h 1 (0 : Fin n) 0
local notation "f₃" => completePointNodeLocalizedPoleThree K n h 1 (0 : Fin n) 0

/-- Further restriction to the actual secant neighborhood of the source node. -/
abbrev CompleteIdentityFirstPoleSecantPatch := Localization.Away (c)
local notation "T" => CompleteIdentityFirstPoleSecantPatch K n h U
local notation "ν" => algebraMap (Z) (T)

/-- The unchanged coordinate error lies in any ideal containing both actual pole errors. -/
theorem completeIdentityFirstPolePatch_error_mem
    (I : Ideal (T))
    (h₂ : (ν) ((Q) (f₂) - (S) (f₂)) ∈ I)
    (h₃ : (ν) ((Q) (f₃) - (S) (f₃)) ∈ I) :
    (ν) ((ι) ((ρ) (completeIdentityFirstAmbientError K n h (leftCoordinate (t))))) ∈ I := by
  rw [← completeIdentityFirstPolePatch_error]
  apply (I.unit_mul_mem_iff_mem (IsLocalization.Away.algebraMap_isUnit (c))).mp
  rw [← (ν).map_mul, completeIdentityFirstPolePatch_error_equation, (ν).map_mul]
  apply I.mul_mem_left
  rw [(ν).map_sub, (ν).map_mul, (ν).map_mul]
  exact I.sub_mem (I.mul_mem_left _ h₃) (I.mul_mem_left _ h₂)

/-- Equality of both retained poles on this neighborhood kills the actual coordinate error. -/
theorem completeIdentityFirstPolePatch_error_eq_zero
    (h₂ : (ν) ((Q) (f₂)) = (ν) ((S) (f₂)))
    (h₃ : (ν) ((Q) (f₃)) = (ν) ((S) (f₃))) :
    (ν) ((ι) ((ρ) (completeIdentityFirstAmbientError K n h (leftCoordinate (t))))) = 0 := by
  apply (Ideal.mem_bot).mp
  apply completeIdentityFirstPolePatch_error_mem K n h U ⊥
  · exact (Ideal.mem_bot).mpr (by rw [(ν).map_sub, h₂, sub_self])
  · exact (Ideal.mem_bot).mpr (by rw [(ν).map_sub, h₃, sub_self])

end FLT.Mazur.PolygonInfinitesimalStages
