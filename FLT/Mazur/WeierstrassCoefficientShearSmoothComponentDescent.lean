/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearSpecializationCartesian
public import FLT.Mazur.WeierstrassCoefficientShearSmoothOrbitLocus
public import FLT.Mazur.SchemeSmoothLocusQuotient
public import FLT.Mazur.QuotientConnectedComponentDescent
public import FLT.Mazur.SchemeOpenRangeRestriction

/-!
# Faithful descent of the original smooth-orbit component

The full retained orbit is saturated for actual coefficient specialization.
A complete component calculation upstairs therefore descends to the original
zero below, with its independently constructed embedding unchanged.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (K L : Type u) [Field K] [Field L] [Algebra R K] [Algebra R L]
  (r : K) (v : L) (j : ℕ) (hj : j ≤ n) (f : K →ₐ[R] L)
local notation "gK" => coefficientShearGluedStructure hπ data K r j hj
local notation "gL" => coefficientShearGluedStructure hπ data L v j hj
local notation "p" => coefficientShearSpecialization hπ data K L r v j hj f
local notation "BK" => coefficientShearSmoothEmbedding hπ data K r j hj
local notation "BL" => coefficientShearSmoothEmbedding hπ data L v j hj
local notation "H" => coefficientShearSpecialization_isPullback hπ data K L r v j hj f
/-- The whole original orbit is saturated under the actual model specialization. -/
theorem coefficientShearSpecialization_preimage_smoothOrbit :
    p ⁻¹' Set.range BK = Set.range BL := by
  rw [coefficientShearSmoothEmbedding_range, coefficientShearSmoothEmbedding_range]
  change (p ≫ coefficientShearGluedProjection hπ data K r j hj) ⁻¹' _ = _
  rw [coefficientShearSpecialization_projection]
  rfl

variable [LocallyOfFinitePresentation (coefficientShearGluedStructure hπ data K r j hj)]
  [LocallyOfFinitePresentation (coefficientShearGluedStructure hπ data L v j hj)]
local notation "m" => SmoothLocusDescent.map H
local notation "bK" => coefficientShearSmoothOrbitToSmooth hπ data K r j hj
local notation "bL" => coefficientShearSmoothOrbitToSmooth hπ data L v j hj

/-- Saturation holds inside the entire relative smooth loci as well. -/
theorem coefficientShearSmoothSpecialization_preimage_orbit :
    m ⁻¹' Set.range bK = Set.range bL := by
  exact OpenRangeRestriction.preimage_range_map p m (gK).smoothLocus.ι (gL).smoothLocus.ι
    bK BK bL BL (SmoothLocusDescent.map_inclusion H)
    (coefficientShearSmoothOrbitToSmooth_inclusion hπ data K r j hj)
    (coefficientShearSmoothOrbitToSmooth_inclusion hπ data L v j hj)
    (coefficientShearSpecialization_preimage_smoothOrbit hπ data K L r v j hj f)

/-- The upstairs component calculation determines the entire original-zero component below. -/
theorem coefficientShearOriginalZero_component_descends
    (hf : f.toRingHom.FaithfullyFlat) (z : (gL).smoothLocus.toScheme)
    (hz : (gL).smoothLocus.ι '' connectedComponent z = Set.range BL)
    (x : Spec (.of K)) :
    (gK).smoothLocus.ι '' connectedComponent
      (coefficientShearOriginalSmoothZero hπ data K r j hj x) = Set.range BK := by
  obtain ⟨hq, hq'⟩ := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom f.toRingHom)).mpr hf
  let _ := hq
  let _ := hq'
  have hc : connectedComponent z = Set.range bL := by
    apply Set.image_injective.mpr (gL).smoothLocus.ι.isOpenEmbedding.injective
    rw [hz, ← Set.range_comp]
    exact (congrArg (fun a : _ ⟶ _ => Set.range a)
      (coefficientShearSmoothOrbitToSmooth_inclusion hπ data L v j hj)).symm
  have hcomp : IsOpenImmersion (bL ≫ (gL).smoothLocus.ι) := by
    rw [coefficientShearSmoothOrbitToSmooth_inclusion]
    infer_instance
  let _ : IsOpenImmersion bL := IsOpenImmersion.of_comp bL (gL).smoothLocus.ι
  have hpre := coefficientShearSmoothSpecialization_preimage_orbit
    hπ data K L r v j hj f
  have he := ComponentDescent.connectedComponent_eq_of_component_preimage
    (SmoothLocusDescent.map_isQuotientMap H) (hpre.trans hc.symm)
    (hpre.symm ▸ (bL).isOpenEmbedding.isOpen_range)
    (y := coefficientShearOriginalSmoothZero hπ data K r j hj x)
    ⟨integralSmoothZero (W.map (algebraMap R K)) x, rfl⟩
  rw [he, ← Set.range_comp]
  exact congrArg (fun a : _ ⟶ _ => Set.range a)
    (coefficientShearSmoothOrbitToSmooth_inclusion hπ data K r j hj)

end FLT.Mazur.WeierstrassDividedDepth
