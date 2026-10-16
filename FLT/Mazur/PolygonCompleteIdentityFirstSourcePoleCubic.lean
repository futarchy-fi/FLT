/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstSourcePoleGeometry
public import FLT.Mazur.PolygonCompleteIdentityFirstSourceZeroCubic
public import FLT.Mazur.PolygonCompleteIdentityAdicCubicZNeighborhood

/-!
# Full parameter quotients on the source pole open land in the cubic Z chart

The original pullback equation and order-zero action law provide an actual
factorization of the target contraction. Only the source marking denominator
has been inverted; arbitrary nilpotents in the receiving ring are retained.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "Z" => CompleteIdentityFirstSourcePolePatch K n h U
local notation "ρ" => completeIdentityFirstAmbientRestriction K n h (V)
local notation "ι" => algebraMap Γ((R), (V).1) (Z)
local notation "τ" => (ι) ((ρ) (completeIdentityFirstAmbientParameter K n h))
local notation "S" => completeIdentityFirstSourcePoleFunctions K n h U
local notation "F" => completeIdentityFirstSourcePoleInputFunctions K n h U
local notation "M" => completeIdentityFirstSourcePolePatchMap K n h U
local notation "E" => completePointWeierstrassCurve K n h (0 : Fin n)
local notation "d" => completePointNodeToCubicChart K n h 1 0 0
variable {B : Type} [CommRing B]
variable (φ : CompleteIdentityFirstSourcePolePatch K n h U →+* B)
variable (hf : φ (completeIdentityFirstSourcePoleParameter K n h U) = 0)

include hf

local notation "p" => (pullback.snd _ _ : (R) ⟶
  PolygonSmoothing.chart (Ring K 1) (parameter K 1))
local notation "a" => PolygonInfinitesimal.chart (Ring K 1) (parameter K 1) n h (0 : Fin n)
local notation "g" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "r" => originalStageToCompatibleProj K n h 1

/-- The target contraction factors through the source cubic chart in every parameter quotient. -/
theorem completeIdentityFirstSourcePole_targetCubic :
    Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (S)) ≫ (d) ≫
        integralCurveChart (E) 2 =
      Spec.map (CommRingCat.ofHom φ) ≫ (M) ≫ (V).1.ι ≫ (p) ≫ (a) ≫ (r) ≫ (g) := by
  rw [completeIdentityFirstSourcePole_universalScaling K n h U,
    ← completeIdentityActionAdicChartSpace_cubic K n h 1 0 0]
  rw [← completeIdentityFirstSourcePoleInputFunctions_map_assoc,
    ← completeIdentityFirstSourcePoleInputFunctions_map_assoc]
  simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  apply completeIdentityFirstSource_cubic_of_parameter_zero K n h 0 (φ.comp (F))
  change φ ((F) _) = 0
  rw [completeIdentityFirstSourcePoleInputFunctions_parameter]
  exact hf

local notation "κ" => completeIdentityActionAdicChartSpaceMap K n h 1 0 0 ≫
  completeIdentityActionAdicLiftSpaceMap K n h 1

/-- Every source-only parameter quotient lands in the actual complete cubic Z open. -/
theorem completeIdentityFirstSourcePole_mem_cubicZ (z : Spec (.of B)) :
    (κ) ((V).1.ι ((M) ((Spec.map (CommRingCat.ofHom φ)) z))) ∈
      completeIdentityCubicChartOpen K n h 2 := by
  have hz : ((p) ≫ (a) ≫ (r) ≫ (g))
      ((V).1.ι ((M) ((Spec.map (CommRingCat.ofHom φ)) z))) ∈
      (integralCurveChart (E) 2).opensRange := by
    refine ⟨((Spec.map (CommRingCat.ofHom φ)) ≫
      Spec.map (CommRingCat.ofHom (S)) ≫ (d)) z, ?_⟩
    exact congrArg (fun f ↦ f z)
      (completeIdentityFirstSourcePole_targetCubic K n h U φ hf)
  have he : (κ) ⁻¹ᵁ completeIdentityCubicChartOpen K n h 2 =
      ((p) ≫ (a) ≫ (r) ≫ (g)) ⁻¹ᵁ (integralCurveChart (E) 2).opensRange := by
    rw [completeIdentityAdicCubicZ_preimage]
    simp only [Scheme.Hom.comp_preimage, completePointToIntegralCubic_preimage_chart]
    rw [completePointStageNodeOpen, completePointStageComplement_preimage]
    rfl
  exact (show (V).1.ι ((M) ((Spec.map (CommRingCat.ofHom φ)) z)) ∈
    (κ) ⁻¹ᵁ completeIdentityCubicChartOpen K n h 2 from he.symm ▸ hz)

end FLT.Mazur.PolygonInfinitesimalStages
