/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAmbientParameterComparison

/-!
# Exact first-stage equations with the actual complete parameter

The chosen lift can be replaced by the complete coefficient parameter.
Membership is expressed by an explicit parameter-power torsion certificate
before reduction. The adic ambient kernel is still retained in full.
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
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U
local notation "p" => completeIdentityAdicAmbientPatchMap K n h 1 0 0 U
local notation "ρ" => completeIdentityFirstAmbientRestriction K n h (V)
local notation "g" => completeIdentityActionGenericSmoothGraph K n h
local notation "t" => AffinePrincipalKernel.restriction (W)
  (completeIdentityActionAmbientParameter K n h)
local notation "I" => completeIdentityFirstCompleteEquationIdeal K n h U

/-- The chosen lift differs from the actual complete parameter only by an adic equation. -/
theorem completeIdentityFirstCompleteParameter_sub_mem :
    completeIdentityFirstCompleteParameter K n h U - (t) ∈ RingHom.ker (p).hom := by
  change (p) (_ - _) = 0
  rw [map_sub, completeIdentityFirstCompleteParameter_spec,
    completeIdentityActionAmbientParameter_patch, sub_self]

/-- The full presentation uses the unchanged complete coefficient parameter. -/
theorem completeIdentityFirstCompleteEquationIdeal_parameter :
    (I) = (RingHom.ker ((g).app (W)).hom ⊔ Ideal.span {(t)}) ⊔ RingHom.ker (p).hom := by
  rw [← completeIdentityFirstCompleteEquationIdeal_comap,
    completeIdentityFirstChartClosedAmbientIdeal_localEquations K n h (V) (W)
      (le_of_eq (completeIdentityAdicAmbientPatch_preimage K n h 1 0 0 U)),
    ← completeIdentityActionAmbientParameter_patch K n h U]
  change (((RingHom.ker ((g).app (W)).hom).map (p).hom) ⊔
    Ideal.span {(p) (t)}).comap (p).hom = _
  rw [← Set.image_singleton, ← Ideal.map_span, ← Ideal.map_sup,
    Ideal.comap_map_of_surjective (p).hom
      (completeIdentityAdicAmbientPatchMap_surjective K n h 1 0 0 U)]
  rfl

/-- An exact torsion certificate for the original full first-stage equation ideal. -/
theorem completeIdentityFirstCompleteEquation_mem_iff
    (z : Γ(completeIdentityActionLiftSpace K n h, (W).1)) :
    z ∈ (I) ↔ ∃ r w, (p) w = 0 ∧ ∃ d : ℕ, (t) ^ d * (z - (t) * r - w) = 0 := by
  rw [completeIdentityFirstCompleteEquationIdeal_parameter]
  constructor
  · intro hz
    obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨a, ha, q, hq, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hq
    refine ⟨r, w, hw, ?_⟩
    have he := (completeIdentityActionGenericSmoothGraph_equation_iff_parameter_torsion
      K n h (W) a).mp ha
    have hr : a + (t) * r + w - (t) * r - w = a := by ring
    rw [hr]
    exact he
  · rintro ⟨r, w, hw, d, hd⟩
    have ha : z - (t) * r - w ∈ RingHom.ker ((g).app (W)).hom :=
      (completeIdentityActionGenericSmoothGraph_equation_iff_parameter_torsion
        K n h (W) _).mpr ⟨d, hd⟩
    apply Submodule.mem_sup.mpr
    refine ⟨z - w, ?_, w, hw, sub_add_cancel _ _⟩
    apply Submodule.mem_sup.mpr
    refine ⟨z - (t) * r - w, ha, (t) * r,
      Ideal.mem_span_singleton.mpr ⟨r, rfl⟩, ?_⟩
    ring

end FLT.Mazur.PolygonInfinitesimalStages
