/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedImmersionOpenKernel
public import FLT.Mazur.PolygonCompleteIdentityAdicRefinedPatches
public import FLT.Mazur.PolygonCompleteIdentityAdicAmbientKernel

/-!
# Literal parameter-power kernels on original node-pair patches

The whole-adic kernel formula now applies to the actual original node-pair
section map, on the refined covering family. No extra open-restriction
kernel survives on these patches.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
  completeIdentityActionLiftSpaceStructure
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ) (i j : Fin n)
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h m i j).toScheme.affineOpens)
local notation "W" => completeIdentityAdicAmbientTargetPatch K n h m i j U
local notation "p" => completeIdentityAdicAmbientPatchMap K n h m i j U
local notation "τ" => AffinePrincipalKernel.restriction (W)
  (completeIdentityActionAmbientParameter K n h)
variable (hU : (completeIdentityAdicAmbientTargetPatch K n h m i j U).1 ≤
  completeIdentityAdicNodeNeighborhood K n h m i j)
include hU

/-- The original node-pair section map has exactly the complete parameter-power kernel. -/
theorem completeIdentityAdicRefinedPatch_kernel :
    RingHom.ker (p).hom = Ideal.span {(τ) ^ (m + 1)} := by
  rw [ClosedImmersionOpenNeighborhood.patch_kernel
    (completeIdentityActionAdicChartSpaceMap K n h m i j)
    (completeIdentityActionAdicLiftSpaceMap K n h m) U hU,
    ← Scheme.Hom.ker_apply, completeIdentityAdicLiftSpaceMap_affineKernel]

/-- Equality of original adic functions is exact divisibility in the complete ambient ring. -/
theorem completeIdentityAdicRefinedPatch_equation_iff
    (z : Γ(completeIdentityActionLiftSpace K n h, (W).1)) :
    (p) z = 0 ↔ (τ) ^ (m + 1) ∣ z := by
  change z ∈ RingHom.ker (p).hom ↔ _
  rw [completeIdentityAdicRefinedPatch_kernel K n h m i j U hU, Ideal.mem_span_singleton]

/-- Two complete lifts of the same original adic function differ by the actual parameter power. -/
theorem completeIdentityAdicRefinedPatch_eq_iff
    (z w : Γ(completeIdentityActionLiftSpace K n h, (W).1)) :
    (p) z = (p) w ↔ (τ) ^ (m + 1) ∣ z - w := by
  rw [← sub_eq_zero, ← map_sub,
    completeIdentityAdicRefinedPatch_equation_iff K n h m i j U hU]

end FLT.Mazur.PolygonInfinitesimalStages
