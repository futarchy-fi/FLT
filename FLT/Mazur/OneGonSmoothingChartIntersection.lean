/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingOverlapCompatibility
public import FLT.Mazur.WeierstrassCoefficientChartPreimage
public import FLT.Mazur.WeierstrassIntegralCurveTwoChartCover

/-!
# The original puncture is the full cubic chart intersection

The node equation shows D(u)=D(v), so the original conductor puncture is
exactly the part of the affine cubic lying in its infinity chart.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart PolygonNodePresentation OneGonTransition
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type*) [Field K]

/-- The two original pinching generators define the same principal open. -/
theorem node_basicOpen_v :
    PrimeSpectrum.basicOpen (v (R := K)) = PrimeSpectrum.basicOpen (u (R := K)) := by
  ext p
  change v ∉ p.asIdeal ↔ u ∉ p.asIdeal
  apply not_congr
  constructor
  · intro hv
    apply p.isPrime.mem_of_pow_mem 3
    have he : u (R := K) ^ 3 = v * (v - u) := by
      linear_combination -relation (R := K)
    rw [he]
    exact p.asIdeal.mul_mem_right _ hv
  · intro hu
    apply p.isPrime.mem_of_pow_mem 2
    have he : v (R := K) ^ 2 = u * (v + u ^ 2) := by
      linear_combination relation (R := K)
    rw [he]
    exact p.asIdeal.mul_mem_right _ hu

/-- The original torus and the cubic infinity chart have the same open image. -/
theorem zeroTorusInclusion_opensRange :
    (zeroTorusInclusion K).opensRange = (integralCurveChart (equation (0 : K)) 1).opensRange := by
  ext x
  change (∃ y, zeroTorusInclusion K y = x) ↔
    ∃ y, integralCurveChart (equation (0 : K)) 1 y = x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(zeroTorusChartIso K).hom y, rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(zeroTorusChartIso K).inv y, ?_⟩
    change ((zeroTorusChartIso K).inv ≫ (zeroTorusChartIso K).hom ≫
      integralCurveChart (equation (0 : K)) 1) y = _
    simp

/-- Pulling the infinity chart back to the original node chart gives its original puncture. -/
theorem zeroNodeInclusion_preimage_torus :
    zeroNodeInclusion K ⁻¹ᵁ (zeroTorusInclusion K).opensRange =
      PrimeSpectrum.basicOpen (u (R := K)) := by
  rw [zeroTorusInclusion_opensRange, zeroNodeInclusion, Scheme.Hom.comp_preimage,
    integralCurveChart_preimage_chart]
  change Spec.map (CommRingCat.ofHom (zeroAffineNodeEquiv K).toRingHom) ⁻¹ᵁ
    PrimeSpectrum.basicOpen (coord (equation (0 : K)) 2 1) = _
  rw [SpecMap_preimage_basicOpen]
  change PrimeSpectrum.basicOpen (zeroAffineNodeEquiv K (coord (equation (0 : K)) 2 1)) = _
  rw [zeroAffineNodeEquiv_y, node_basicOpen_v]

/-- The actual original overlap is cartesian in the zero-parameter cubic. -/
theorem zeroChart_isPullback :
    IsPullback (bPuncture K) (toTorus K) (zeroNodeInclusion K) (zeroTorusInclusion K) := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback _ _ _ _ (zeroChart_compatibility K)
  apply TopologicalSpace.Opens.ext
  ext x
  change x ∈ zeroNodeInclusion K ⁻¹ᵁ (zeroTorusInclusion K).opensRange ↔
    x ∈ Set.range (bPuncture K)
  rw [zeroNodeInclusion_preimage_torus, range_bPuncture]
  rfl

/-- The two original one-gon charts cover every point of the actual cubic. -/
theorem zeroCharts_cover (x : integralCurve (equation (0 : K))) :
    (∃ y, zeroNodeInclusion K y = x) ∨ ∃ y, zeroTorusInclusion K y = x := by
  rcases integralCurve_yz_cover (equation (0 : K)) x with ⟨y, hy⟩ | ⟨y, hy⟩
  · right
    refine ⟨(zeroTorusChartIso K).inv y, ?_⟩
    change ((zeroTorusChartIso K).inv ≫ (zeroTorusChartIso K).hom ≫
      integralCurveChart (equation (0 : K)) 1) y = x
    simpa using hy
  · left
    refine ⟨(zeroNodeChartIso K).inv y, ?_⟩
    change ((zeroNodeChartIso K).inv ≫ (zeroNodeChartIso K).hom ≫
      integralCurveChart (equation (0 : K)) 2) y = x
    simpa using hy

end FLT.Mazur.OneGonSmoothing
