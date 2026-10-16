/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphParameterTorsion
public import FLT.Mazur.PolygonCompleteIdentityFirstChartLocalEquations

/-!
# Cancel the actual complete parameter before reducing graph equations

The full generic and smooth graph kernels are saturated under every power
of the original complete parameter. The divided equations then specialize
into the unchanged full first-chart ideal, with the original ambient map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
  completeIdentityActionGenericSmoothGraph completeIdentityActionLiftSpaceStructure
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (W : (completeIdentityActionLiftSpace K n h).affineOpens)
local notation "t" => AffinePrincipalKernel.restriction W
  (completeIdentityActionAmbientParameter K n h)
local notation "f" => completeIdentityActionSmoothGraph K n h
local notation "g" => completeIdentityActionGenericSmoothGraph K n h

/-- Complete parameter powers cancel in the actual generic graph equation kernel. -/
theorem completeIdentityActionGenericSmoothGraph_parameter_cancel_iff (d : ℕ)
    (z : Γ(completeIdentityActionLiftSpace K n h, W)) :
    (g).app W ((t) ^ d * z) = 0 ↔ (g).app W z = 0 := by
  constructor
  · intro hz
    obtain ⟨r, hr⟩ :=
      (completeIdentityActionGenericSmoothGraph_equation_iff_parameter_torsion
        K n h W _).mp hz
    apply (completeIdentityActionGenericSmoothGraph_equation_iff_parameter_torsion
      K n h W z).mpr
    exact ⟨r + d, by simpa only [pow_add, mul_assoc] using hr⟩
  · intro hz
    rw [map_mul, hz, mul_zero]

/-- The identical cancellation holds on the full smooth graph before any specialization. -/
theorem completeIdentityActionSmoothGraph_parameter_cancel_iff (d : ℕ)
    (z : Γ(completeIdentityActionLiftSpace K n h, W)) :
    (f).app W ((t) ^ d * z) = 0 ↔ (f).app W z = 0 := by
  change (t) ^ d * z ∈ RingHom.ker ((f).app W).hom ↔
    z ∈ RingHom.ker ((f).app W).hom
  rw [completeIdentityActionSmoothGraph_affineKernel]
  exact completeIdentityActionGenericSmoothGraph_parameter_cancel_iff K n h W d z

local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "k" => completeIdentityActionAdicChartSpaceMap K n h 1 0 0 ≫
  completeIdentityActionAdicLiftSpaceMap K n h 1

/-- First cancel on the complete graph, then restrict the divided equation to the full fiber. -/
theorem completeIdentityFirstChartClosedLocalParameterEquation
    (U : (R).affineOpens) (e : U.1 ≤ (k) ⁻¹ᵁ W.1) (d : ℕ)
    (z : Γ(completeIdentityActionLiftSpace K n h, W))
    (hz : (g).app W ((t) ^ d * z) = 0) :
    (k).appLE W U e z ∈ (completeIdentityFirstChartClosedAmbientIdeal K n h).map
      (completeIdentityFirstAmbientRestriction K n h U).hom :=
  completeIdentityFirstChartClosedLocalEquation K n h U W e z
    ((completeIdentityActionGenericSmoothGraph_parameter_cancel_iff K n h W d z).mp hz)

end FLT.Mazur.PolygonInfinitesimalStages
