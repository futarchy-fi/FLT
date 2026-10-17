/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopSourceIncomingCubic
public import FLT.Mazur.PolygonCompleteIdentityTopSourceTargetComplement
public import FLT.Mazur.PolygonCompletePointTopLocalCubicComparison

/-!
# Exact higher source-node comparison in full local graph tests

The original outgoing and incoming cubic comparisons identify both coordinates
in parameter-zero local receiving rings. Every other nilpotent is retained.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h (m + 1) 0 0).toScheme.affineOpens)
local notation "t" => parameter K (m + 1)
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h (m + 1) 0 0 U
local notation "S" => completeIdentityTopSourcePoleFunctions K n h m U
local notation "Q" => completeIdentityTopSourcePoleTargetFunctions K n h m U
local notation "η" => algebraMap (ChartRing (t)) (StageNodeLocalization K (m + 1))
local notation "ρ" => completeIdentityTopAmbientRestriction K n h m (V)
local notation "ι" => algebraMap _ (CompleteIdentityTopSourcePolePatch K n h m U)

/-- The scaled source retains exactly the original ambient parameter. -/
theorem completeIdentityTopSourcePoleFunctions_parameter :
    (S) ((η) (algebraMap (Ring K (m + 1)) (ChartRing (t)) (t))) =
      completeIdentityTopSourcePoleParameter K n h m U := by
  rw [completeIdentityTopSourcePoleFunctions_algebraMap]
  dsimp only [completeIdentityTopPoleSource, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [ringMap_scalar, AlgHom.commutes, stageCoefficientMap_parameter]
  rfl

variable {B : Type} [CommRing B] [IsLocalRing B]
variable (φ : CompleteIdentityTopSourcePolePatch K n h m U →+* B)
variable (hf : φ (completeIdentityTopSourcePoleParameter K n h m U) = 0)
variable (w : Spec (.of B) ⟶ completeIdentityActionGraphAdicChart K n h (m + 1) 0 0)
variable (hw : w ≫ completeIdentityActionGraphAdicChartEmbedding K n h (m + 1) 0 0 =
  Spec.map (CommRingCat.ofHom φ) ≫ completeIdentityTopSourcePolePatchMap K n h m U ≫
    Scheme.Opens.ι ((completeIdentityAdicAmbientSourcePatch K n h (m + 1) 0 0 U).1))
variable (hx : φ (completeIdentityTopSourcePoleFunctions K n h m U
  (algebraMap (ChartRing (parameter K (m + 1))) (StageNodeLocalization K (m + 1))
    (leftCoordinate (parameter K (m + 1))))) ∈ IsLocalRing.maximalIdeal B)
variable (hy : φ (completeIdentityTopSourcePoleFunctions K n h m U
  (algebraMap (ChartRing (parameter K (m + 1))) (StageNodeLocalization K (m + 1))
    (rightCoordinate (parameter K (m + 1))))) ∈ IsLocalRing.maximalIdeal B)

include hf hw hx hy

/-- Both original target coordinates equal the scaled source in the entire local receiving ring. -/
theorem completeIdentityTopSourcePole_coordinates_eq :
    φ ((Q) (leftCoordinate (t))) = φ ((S) ((η) (leftCoordinate (t)))) ∧
      φ ((Q) (rightCoordinate (t))) = φ ((S) ((η) (rightCoordinate (t)))) := by
  let f := φ.comp (Q)
  let g := φ.comp ((S).comp (η))
  have hc : ∀ z : Ring K (m + 1),
      f (algebraMap (Ring K (m + 1)) (ChartRing (t)) z) =
        g (algebraMap (Ring K (m + 1)) (ChartRing (t)) z) := by
    intro z
    exact congrArg φ (completeIdentityTopSourcePoleTargetFunctions_coefficients K n h m U z)
  have hg : g (algebraMap (Ring K (m + 1)) (ChartRing (t)) (t)) = 0 := by
    change φ ((S) ((η) _)) = 0
    rw [completeIdentityTopSourcePoleFunctions_parameter]
    exact hf
  have ht : f (algebraMap (Ring K (m + 1)) (ChartRing (t)) (t)) = 0 :=
    (hc (t)).trans hg
  apply completePointTopLocalCubic_coordinates K n h 0 m f g ht hg hx hy hc
  · have he := completeIdentityTopSourcePole_targetCubic K n h m U φ hf
    rw [completePointNodeToCubicChart_inclusion] at he
    simpa only [f, g, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
      completeIdentityTopSourcePoleTargetFunctions_map] using he
  · have he := completeIdentityTopSourcePole_incomingCubic K n h m U φ hf w hw
    rw [completePointNodeToCubicChart_inclusion] at he
    simpa only [f, g, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc] using he

/-- Both unchanged ambient errors vanish on full local graph tests at a source-node point. -/
theorem completeIdentityTopSourcePole_errors_zero_of_source_mem :
    φ ((ι) ((ρ) (completeIdentityTopAmbientError K n h m (leftCoordinate (t))))) = 0 ∧
      φ ((ι) ((ρ) (completeIdentityTopAmbientError K n h m (rightCoordinate (t))))) = 0 := by
  obtain ⟨hl, hr⟩ := completeIdentityTopSourcePole_coordinates_eq K n h m U φ hf w hw hx hy
  constructor
  · rw [← completeIdentityTopSourcePoleTargetFunctions_error, map_sub, hl, sub_self]
  · rw [← completeIdentityTopSourcePoleTargetFunctions_error, map_sub, hr, sub_self]

end FLT.Mazur.PolygonInfinitesimalStages
