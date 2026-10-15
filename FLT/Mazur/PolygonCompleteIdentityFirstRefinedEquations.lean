/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAdicRefinedKernel
public import FLT.Mazur.PolygonCompleteIdentityFirstParameterEquations

/-!
# First closed-fiber equations on refined complete ambient patches

The actual adic kernel is absorbed by the original parameter ideal. Thus
the full original first closed-fiber presentation is precisely the generic
graph kernel plus that parameter, on a cover of the original node relation.
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
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
local notation "W" => completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U
local notation "p" => completeIdentityAdicAmbientPatchMap K n h 1 0 0 U
local notation "g" => completeIdentityActionGenericSmoothGraph K n h
local notation "τ" => AffinePrincipalKernel.restriction (W)
  (completeIdentityActionAmbientParameter K n h)
local notation "I" => completeIdentityFirstCompleteEquationIdeal K n h U
variable (hU : (completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U).1 ≤
  completeIdentityAdicNodeNeighborhood K n h 1 0 0)
include hU

/-- On refined patches the original adic ambient equations are already parameter multiples. -/
theorem completeIdentityFirstRefinedPatch_kernel_le :
    RingHom.ker (p).hom ≤ Ideal.span {(τ)} := by
  rw [completeIdentityAdicRefinedPatch_kernel K n h 1 0 0 U hU]
  apply Ideal.span_le.mpr
  intro z hz
  rcases Set.mem_singleton_iff.mp hz with rfl
  exact Ideal.mem_span_singleton.mpr (dvd_pow_self (τ) (by decide : 1 + 1 ≠ 0))

/-- The full original closed-fiber ideal has no extra adic term on this covering family. -/
theorem completeIdentityFirstRefinedEquationIdeal :
    (I) = RingHom.ker ((g).app (W)).hom ⊔ Ideal.span {(τ)} := by
  rw [completeIdentityFirstCompleteEquationIdeal_parameter, sup_eq_left]
  exact (completeIdentityFirstRefinedPatch_kernel_le K n h U hU).trans le_sup_right

/-- Exact original equation membership uses only a complete parameter-torsion certificate. -/
theorem completeIdentityFirstRefinedEquation_mem_iff
    (z : Γ(completeIdentityActionLiftSpace K n h, (W).1)) :
    z ∈ (I) ↔ ∃ r, ∃ d : ℕ, (τ) ^ d * (z - (τ) * r) = 0 := by
  rw [completeIdentityFirstRefinedEquationIdeal K n h U hU]
  constructor
  · intro hz
    obtain ⟨v, hv, q, hq, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hq
    refine ⟨r, ?_⟩
    rw [add_sub_cancel_right]
    exact (completeIdentityActionGenericSmoothGraph_equation_iff_parameter_torsion
      K n h (W) v).mp hv
  · rintro ⟨r, d, hd⟩
    apply Submodule.mem_sup.mpr
    refine ⟨z - (τ) * r, ?_, (τ) * r,
      Ideal.mem_span_singleton.mpr ⟨r, rfl⟩, sub_add_cancel _ _⟩
    exact (completeIdentityActionGenericSmoothGraph_equation_iff_parameter_torsion
      K n h (W) _).mpr ⟨d, hd⟩

end FLT.Mazur.PolygonInfinitesimalStages
