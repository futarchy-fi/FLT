/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopAffineGraphTests
public import FLT.Mazur.PolygonCompleteIdentityTopSourceLocalComparison

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
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h (m + 1) 0 0).toScheme.affineOpens)
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h (m + 1) 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h (m + 1) 0 0
local notation "f" => completeIdentityActionGraphAdicChartEmbedding K n h (m + 1) 0 0
local notation "M" => completeIdentityTopSourcePolePatchMap K n h m U
variable {B : Type} [CommRing B]
variable (ψ : Γ(completeIdentityActionAdicChartSpace K n h (m + 1) 0 0,
  (completeIdentityAdicAmbientSourcePatch K n h (m + 1) 0 0 U).1) →+* B)
variable [IsLocalRing B]
local notation "A" => Γ((R), (V).1)
local notation "Z" => CompleteIdentityTopSourcePolePatch K n h m U
local notation "ι" => algebraMap (A) (Z)
/-- Cache the existing affine patch ring structure for the local lifting calculation. -/
local instance topLocalTestPatchCommRing : CommRing (Γ((R), (V).1)) := inferInstance
attribute [local irreducible] completeIdentityTopPoleSource
local notation "s" => completeIdentityTopPoleSource K n h m U
local notation "t" => parameter K (m + 1)
local notation "d" => nodeMarkingDenominator (t)
local notation "ρ" => completeIdentityTopAmbientRestriction K n h m (V)
variable (hx : ψ (completeIdentityTopPoleSource K n h m U
  (leftCoordinate (parameter K (m + 1)))) ∈ IsLocalRing.maximalIdeal B)
variable (hy : ψ (completeIdentityTopPoleSource K n h m U
  (rightCoordinate (parameter K (m + 1)))) ∈ IsLocalRing.maximalIdeal B)

include hx hy

/-- Only the actual source marking denominator needs to be inverted. -/
theorem completeIdentityTopLocalTest_source_denominator : IsUnit (ψ ((s) (d))) := by
  rw [nodeMarkingDenominator, (s).map_mul, (s).map_sub, (s).map_sub, (s).map_one,
    ψ.map_mul, ψ.map_sub, ψ.map_sub, ψ.map_one]
  exact (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hx).mul
    (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hy)

/-- Extend the full local test along the source-only pole localization. -/
def completeIdentityTopLocalTestSourceLift : (Z) →+* B :=
  IsLocalization.Away.lift ((s) (d)) (g := ψ)
    (completeIdentityTopLocalTest_source_denominator K n h m U ψ hx hy)
local notation "φ" => completeIdentityTopLocalTestSourceLift K n h m U ψ hx hy

/-- No element of the original affine receiving map is changed by the extension. -/
theorem completeIdentityTopLocalTestSourceLift_algebraMap (z : A) :
    (φ) ((ι) z) = ψ z := IsLocalization.Away.lift_eq _ _ _

variable (hI : (completeIdentityActionGraphAdicChartEmbedding K n h (m + 1) 0 0).ker.ideal
  (completeIdentityAdicAmbientSourcePatch K n h (m + 1) 0 0 U) ≤ RingHom.ker ψ)
variable (ht : ψ (completeIdentityTopAmbientRestriction K n h m
  (completeIdentityAdicAmbientSourcePatch K n h (m + 1) 0 0 U)
    (completeIdentityTopAmbientParameter K n h m)) = 0)
include hI ht

/-- The unchanged full graph and parameter imply both coordinate-error equations locally. -/
theorem completeIdentityTopLocalTest_errors_zero :
    ψ ((ρ) (completeIdentityTopAmbientError K n h m (leftCoordinate (t)))) = 0 ∧
      ψ ((ρ) (completeIdentityTopAmbientError K n h m (rightCoordinate (t)))) = 0 := by
  let w := completeIdentityTopAffineTestToGraph K n h m U ψ hI
  have hw : w ≫ (f) = Spec.map (CommRingCat.ofHom (φ)) ≫ (M) ≫ (V).1.ι := by
    have he : (φ).comp (ι) = ψ := by
      apply RingHom.ext
      exact completeIdentityTopLocalTestSourceLift_algebraMap K n h m U ψ hx hy
    rw [completeIdentityTopAffineTestToGraph_inclusion,
      completeIdentityTopSourcePolePatchMap, AffineOpenSpectrumFunctions.map]
    simp only [Category.assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      he, IsAffineOpen.isoSpec_inv_ι]
  have hp : (φ) (completeIdentityTopSourcePoleParameter K n h m U) = 0 := by
    rw [completeIdentityTopSourcePoleParameter,
      completeIdentityTopLocalTestSourceLift_algebraMap]
    exact ht
  have he := completeIdentityTopSourcePole_errors_zero_of_source_mem K n h m U (φ) hp w hw
  simp only [completeIdentityTopSourcePoleFunctions_algebraMap,
    completeIdentityTopLocalTestSourceLift_algebraMap] at he
  exact he hx hy

/-- Both coordinate equations determine all original node-function errors in this local test. -/
theorem completeIdentityTopLocalTest_all_errors_zero (z : ChartRing (t)) :
    ψ ((ρ) (completeIdentityTopAmbientError K n h m z)) = 0 := by
  let Q := completeIdentityTopSourcePoleTargetFunctions K n h m U
  let S := completeIdentityTopSourcePoleFunctions K n h m U
  let η := algebraMap (ChartRing (t)) (StageNodeLocalization K (m + 1))
  have hxy := completeIdentityTopLocalTest_errors_zero K n h m U ψ hx hy hI ht
  have he : (φ).comp Q = (φ).comp (S.comp η) := by
    apply chartRing_ringHom_ext
    · intro c
      exact congrArg φ (completeIdentityTopSourcePoleTargetFunctions_coefficients K n h m U c)
    · apply sub_eq_zero.mp
      change φ (Q (leftCoordinate (t))) - φ (S (η (leftCoordinate (t)))) = 0
      rw [← map_sub, completeIdentityTopSourcePoleTargetFunctions_error,
        completeIdentityTopLocalTestSourceLift_algebraMap]
      exact hxy.1
    · apply sub_eq_zero.mp
      change φ (Q (rightCoordinate (t))) - φ (S (η (rightCoordinate (t)))) = 0
      rw [← map_sub, completeIdentityTopSourcePoleTargetFunctions_error,
        completeIdentityTopLocalTestSourceLift_algebraMap]
      exact hxy.2
  have hz := DFunLike.congr_fun he z
  change φ (Q z) = φ (S (η z)) at hz
  have hz' := sub_eq_zero.mpr hz
  rw [← map_sub, completeIdentityTopSourcePoleTargetFunctions_error,
    completeIdentityTopLocalTestSourceLift_algebraMap] at hz'
  exact hz'

end FLT.Mazur.PolygonInfinitesimalStages
