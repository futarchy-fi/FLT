/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstAffineGraphTests
public import FLT.Mazur.PolygonCompleteIdentityFirstSourceLocalComparison

/-!
# Full local affine graph tests kill the original coordinate errors

Every local receiving map from an original affine patch that kills the
full graph ideal and parameter identifies both actual coordinates at a
source-node point. Source coordinates need only belong to the maximal
ideal; their nilpotent values are retained.
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
  FCurve.ModuleSheafTensor.tensor FCurve.divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "f" => completeIdentityActionGraphAdicChartEmbedding K n h 1 0 0
local notation "M" => completeIdentityFirstSourcePolePatchMap K n h U
variable {B : Type} [CommRing B]
variable (ψ : Γ(completeIdentityActionAdicChartSpace K n h 1 0 0,
  (completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U).1) →+* B)
variable [IsLocalRing B]
local notation "A" => Γ((R), (V).1)
local notation "Z" => CompleteIdentityFirstSourcePolePatch K n h U
local notation "ι" => algebraMap (A) (Z)
/-- Cache the existing affine patch ring structure for the local lifting calculation. -/
local instance localTestPatchCommRing : CommRing (Γ((R), (V).1)) := inferInstance
attribute [local irreducible] completeIdentityFirstPoleSource
local notation "s" => completeIdentityFirstPoleSource K n h U
local notation "t" => parameter K 1
local notation "d" => nodeMarkingDenominator (t)
local notation "ρ" => completeIdentityFirstAmbientRestriction K n h (V)
variable (hx : ψ (completeIdentityFirstPoleSource K n h U
  (leftCoordinate (parameter K 1))) ∈ IsLocalRing.maximalIdeal B)
variable (hy : ψ (completeIdentityFirstPoleSource K n h U
  (rightCoordinate (parameter K 1))) ∈ IsLocalRing.maximalIdeal B)

include hx hy

/-- Only the actual source marking denominator needs to be inverted. -/
theorem completeIdentityFirstLocalTest_source_denominator : IsUnit (ψ ((s) (d))) := by
  rw [nodeMarkingDenominator, (s).map_mul, (s).map_sub, (s).map_sub, (s).map_one,
    ψ.map_mul, ψ.map_sub, ψ.map_sub, ψ.map_one]
  exact (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hx).mul
    (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hy)

/-- Extend the full local test along the source-only pole localization. -/
def completeIdentityFirstLocalTestSourceLift : (Z) →+* B :=
  IsLocalization.Away.lift ((s) (d)) (g := ψ)
    (completeIdentityFirstLocalTest_source_denominator K n h U ψ hx hy)
local notation "φ" => completeIdentityFirstLocalTestSourceLift K n h U ψ hx hy

/-- No element of the original affine receiving map is changed by the extension. -/
theorem completeIdentityFirstLocalTestSourceLift_algebraMap (z : A) :
    (φ) ((ι) z) = ψ z := IsLocalization.Away.lift_eq _ _ _

variable (hI : (completeIdentityActionGraphAdicChartEmbedding K n h 1 0 0).ker.ideal
  (completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U) ≤ RingHom.ker ψ)
variable (ht : ψ (completeIdentityFirstAmbientRestriction K n h
  (completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U)
    (completeIdentityFirstAmbientParameter K n h)) = 0)
include hI ht

/-- The unchanged full graph and parameter imply both coordinate-error equations locally. -/
theorem completeIdentityFirstLocalTest_errors_zero :
    ψ ((ρ) (completeIdentityFirstAmbientError K n h (leftCoordinate (t)))) = 0 ∧
      ψ ((ρ) (completeIdentityFirstAmbientError K n h (rightCoordinate (t)))) = 0 := by
  let w := completeIdentityFirstAffineTestToGraph K n h U ψ hI
  have hw : w ≫ (f) = Spec.map (CommRingCat.ofHom (φ)) ≫ (M) ≫ (V).1.ι := by
    have he : (φ).comp (ι) = ψ := by
      apply RingHom.ext
      exact completeIdentityFirstLocalTestSourceLift_algebraMap K n h U ψ hx hy
    rw [completeIdentityFirstAffineTestToGraph_inclusion,
      completeIdentityFirstSourcePolePatchMap, AffineOpenSpectrumFunctions.map]
    simp only [Category.assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      he, IsAffineOpen.isoSpec_inv_ι]
  have hp : (φ) (completeIdentityFirstSourcePoleParameter K n h U) = 0 := by
    rw [completeIdentityFirstSourcePoleParameter,
      completeIdentityFirstLocalTestSourceLift_algebraMap]
    exact ht
  have he := completeIdentityFirstSourcePole_errors_zero_of_source_mem K n h U (φ) hp w hw
  simp only [completeIdentityFirstSourcePoleFunctions_algebraMap,
    completeIdentityFirstLocalTestSourceLift_algebraMap] at he
  exact he hx hy

/-- Both coordinate equations determine all original node-function errors in this local test. -/
theorem completeIdentityFirstLocalTest_all_errors_zero (z : ChartRing (t)) :
    ψ ((ρ) (completeIdentityFirstAmbientError K n h z)) = 0 := by
  let Q := completeIdentityFirstSourcePoleTargetFunctions K n h U
  let S := completeIdentityFirstSourcePoleFunctions K n h U
  let η := algebraMap (ChartRing (t)) (StageNodeLocalization K 1)
  have hxy := completeIdentityFirstLocalTest_errors_zero K n h U ψ hx hy hI ht
  have he : (φ).comp Q = (φ).comp (S.comp η) := by
    apply chartRing_ringHom_ext
    · intro c
      exact congrArg φ (completeIdentityFirstSourcePoleTargetFunctions_coefficients K n h U c)
    · apply sub_eq_zero.mp
      change φ (Q (leftCoordinate (t))) - φ (S (η (leftCoordinate (t)))) = 0
      rw [← map_sub, completeIdentityFirstSourcePoleTargetFunctions_error,
        completeIdentityFirstLocalTestSourceLift_algebraMap]
      exact hxy.1
    · apply sub_eq_zero.mp
      change φ (Q (rightCoordinate (t))) - φ (S (η (rightCoordinate (t)))) = 0
      rw [← map_sub, completeIdentityFirstSourcePoleTargetFunctions_error,
        completeIdentityFirstLocalTestSourceLift_algebraMap]
      exact hxy.2
  have hz := DFunLike.congr_fun he z
  change φ (Q z) = φ (S (η z)) at hz
  have hz' := sub_eq_zero.mpr hz
  rw [← map_sub, completeIdentityFirstSourcePoleTargetFunctions_error,
    completeIdentityFirstLocalTestSourceLift_algebraMap] at hz'
  exact hz'

end FLT.Mazur.PolygonInfinitesimalStages
