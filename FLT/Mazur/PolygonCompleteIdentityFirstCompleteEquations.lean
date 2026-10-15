/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstCompleteErrors
public import FLT.Mazur.PolygonCompleteIdentityFirstChartLocalEquations

/-!
# The full first closed fiber presented in original complete affine coordinates

On each transported affine patch the complete presentation ideal is the sum
of the generic graph kernel, the original adic ambient kernel, and a lift of
the original parameter. This gives an exact membership test for the actual
errors; it does not assert that these errors belong to that ideal.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
  completeIdentityActionGenericSmoothGraph
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "W" => completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U
local notation "p" => completeIdentityAdicAmbientPatchMap K n h 1 0 0 U
local notation "ρ" => completeIdentityFirstAmbientRestriction K n h (V)
local notation "J" => completeIdentityFirstChartClosedAmbientIdeal K n h
local notation "g" => completeIdentityActionGenericSmoothGraph K n h
local notation "t" => completeIdentityFirstAmbientParameter K n h

/-- A complete ambient representative of the original parameter on the actual stage. -/
def completeIdentityFirstCompleteParameter :
    Γ(completeIdentityActionLiftSpace K n h, (W).1) :=
  completeIdentityAdicAmbientLift K n h 1 0 0 U (t)
local notation "T" => completeIdentityFirstCompleteParameter K n h U

/-- This parameter is lifted before the closed-fiber quotient is imposed. -/
theorem completeIdentityFirstCompleteParameter_spec : (p) (T) = (ρ) (t) :=
  completeIdentityAdicAmbientLift_spec K n h 1 0 0 U (t)

/-- The full original closed-fiber ideal expressed in the original complete affine ring. -/
def completeIdentityFirstCompleteEquationIdeal :
    Ideal Γ(completeIdentityActionLiftSpace K n h, (W).1) :=
  (RingHom.ker ((g).app (W)).hom ⊔ Ideal.span {(T)}) ⊔ RingHom.ker (p).hom
local notation "I" => completeIdentityFirstCompleteEquationIdeal K n h U

/-- The original full closed-fiber ideal is the image of the complete equations. -/
theorem completeIdentityFirstCompleteEquationIdeal_map : (I).map (p).hom = (J).map (ρ).hom := by
  have hk : (RingHom.ker (p).hom).map (p).hom = ⊥ :=
    (Ideal.map_eq_bot_iff_le_ker _).mpr le_rfl
  rw [completeIdentityFirstCompleteEquationIdeal, Ideal.map_sup, Ideal.map_sup,
    Ideal.map_span, Set.image_singleton, completeIdentityFirstCompleteParameter_spec,
    hk, sup_bot_eq]
  exact (completeIdentityFirstChartClosedAmbientIdeal_localEquations K n h (V) (W)
    (le_of_eq (completeIdentityAdicAmbientPatch_preimage K n h 1 0 0 U))).symm

/-- Pulling back retains the adic ambient kernel, not only the generic smooth-graph equations. -/
theorem completeIdentityFirstCompleteEquationIdeal_comap :
    ((J).map (ρ).hom).comap (p).hom = (I) := by
  rw [completeIdentityFirstChartClosedAmbientIdeal_localEquations K n h (V) (W)
    (le_of_eq (completeIdentityAdicAmbientPatch_preimage K n h 1 0 0 U))]
  rw [← completeIdentityFirstCompleteParameter_spec K n h U]
  change (((RingHom.ker ((g).app (W)).hom).map (p).hom) ⊔
    Ideal.span {(p) (T)}).comap (p).hom = _
  rw [← Set.image_singleton, ← Ideal.map_span, ← Ideal.map_sup,
    Ideal.comap_map_of_surjective (p).hom
      (completeIdentityAdicAmbientPatchMap_surjective K n h 1 0 0 U)]
  rfl

/-- The constructed error has its exact original ideal-membership test in complete coordinates. -/
theorem completeIdentityFirstCompleteError_mem_iff
    (z : PolygonSmoothing.ChartRing (parameter K 1)) :
    completeIdentityFirstCompleteError K n h U z ∈ (I) ↔
      (ρ) (completeIdentityFirstAmbientError K n h z) ∈ (J).map (ρ).hom := by
  rw [← completeIdentityFirstCompleteEquationIdeal_comap, Ideal.mem_comap,
    completeIdentityFirstCompleteError_spec]

end FLT.Mazur.PolygonInfinitesimalStages
