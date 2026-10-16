/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopSourcePoleGeometry
public import FLT.Mazur.PolygonCompleteIdentityStageSourceZeroCubic
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
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h (m + 1) 0 0).toScheme.affineOpens)
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h (m + 1) 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h (m + 1) 0 0
local notation "Z" => CompleteIdentityTopSourcePolePatch K n h m U
local notation "ρ" => completeIdentityTopAmbientRestriction K n h m (V)
local notation "ι" => algebraMap Γ((R), (V).1) (Z)
local notation "τ" => (ι) ((ρ) (completeIdentityTopAmbientParameter K n h m))
local notation "S" => completeIdentityTopSourcePoleFunctions K n h m U
local notation "F" => completeIdentityTopSourcePoleInputFunctions K n h m U
local notation "M" => completeIdentityTopSourcePolePatchMap K n h m U
local notation "E" => completePointWeierstrassCurve K n h (0 : Fin n)
local notation "d" => completePointNodeToCubicChart K n h (m + 1) 0 0
variable {B : Type} [CommRing B]
variable (φ : CompleteIdentityTopSourcePolePatch K n h m U →+* B)
variable (hf : φ (completeIdentityTopSourcePoleParameter K n h m U) = 0)

include hf

local notation "p" => (pullback.snd _ _ : (R) ⟶
  PolygonSmoothing.chart (Ring K (m + 1)) (parameter K (m + 1)))
local notation "a" => PolygonInfinitesimal.chart
  (Ring K (m + 1)) (parameter K (m + 1)) n h (0 : Fin n)
local notation "g" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "r" => originalStageToCompatibleProj K n h (m + 1)

/-- The target contraction factors through the source cubic chart in every parameter quotient. -/
theorem completeIdentityTopSourcePole_targetCubic :
    Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (S)) ≫ (d) ≫
        integralCurveChart (E) 2 =
      Spec.map (CommRingCat.ofHom φ) ≫ (M) ≫ (V).1.ι ≫ (p) ≫ (a) ≫ (r) ≫ (g) := by
  rw [completeIdentityTopSourcePole_universalScaling K n h m U,
    ← completeIdentityActionAdicChartSpace_cubic K n h (m + 1) 0 0]
  rw [← completeIdentityTopSourcePoleInputFunctions_map_assoc,
    ← completeIdentityTopSourcePoleInputFunctions_map_assoc]
  simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  apply completeIdentityStageSource_cubic_of_parameter_zero K n h 0 (m + 1) (φ.comp (F))
  change φ ((F) _) = 0
  rw [completeIdentityTopSourcePoleInputFunctions_parameter]
  exact hf

local notation "κ" => completeIdentityActionAdicChartSpaceMap K n h (m + 1) 0 0 ≫
  completeIdentityActionAdicLiftSpaceMap K n h (m + 1)

/-- Every source-only parameter quotient lands in the actual complete cubic Z open. -/
theorem completeIdentityTopSourcePole_mem_cubicZ (z : Spec (.of B)) :
    (κ) ((V).1.ι ((M) ((Spec.map (CommRingCat.ofHom φ)) z))) ∈
      completeIdentityCubicChartOpen K n h 2 := by
  have hz : ((p) ≫ (a) ≫ (r) ≫ (g))
      ((V).1.ι ((M) ((Spec.map (CommRingCat.ofHom φ)) z))) ∈
      (integralCurveChart (E) 2).opensRange := by
    refine ⟨((Spec.map (CommRingCat.ofHom φ)) ≫
      Spec.map (CommRingCat.ofHom (S)) ≫ (d)) z, ?_⟩
    exact congrArg (fun f ↦ f z)
      (completeIdentityTopSourcePole_targetCubic K n h m U φ hf)
  have he : (κ) ⁻¹ᵁ completeIdentityCubicChartOpen K n h 2 =
      ((p) ≫ (a) ≫ (r) ≫ (g)) ⁻¹ᵁ (integralCurveChart (E) 2).opensRange := by
    rw [completeIdentityAdicCubicZ_preimage]
    simp only [Scheme.Hom.comp_preimage, completePointToIntegralCubic_preimage_chart]
    rw [completePointStageNodeOpen, completePointStageComplement_preimage]
    rfl
  exact (show (V).1.ι ((M) ((Spec.map (CommRingCat.ofHom φ)) z)) ∈
    (κ) ⁻¹ᵁ completeIdentityCubicChartOpen K n h 2 from he.symm ▸ hz)

end FLT.Mazur.PolygonInfinitesimalStages
