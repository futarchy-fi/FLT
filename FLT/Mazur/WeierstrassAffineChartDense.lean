/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralCurveTwoChartCover
public import FLT.Mazur.WeierstrassProductOverlapFlat

/-!
# Density of the affine chart in the actual cubic

The regular Z coordinate makes the infinity-chart localization injective.
Its spectrum is dense, so the affine chart is dense in the whole glued cubic,
including over nonreduced coefficient rings and for singular cubics.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The affine overlap is dense in the infinity chart over every coefficient ring. -/
theorem infinityOverlap_denseRange : DenseRange (overlapInclusion W 1 2) := by
  change DenseRange (PrimeSpectrum.comap (overlapRestriction W 1 2).toRingHom)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot (overlapRestriction W 1 2).toRingHom).mp
      (infinityOverlapRestriction_injective W)]
  exact bot_le

/-- Every point at infinity is in the closure of the affine chart. -/
theorem infinityChart_subset_affine_closure :
    Set.range (integralCurveChart W 1) ⊆ closure (Set.range (integralCurveChart W 2)) := by
  rintro _ ⟨x, rfl⟩
  have h : closure (Set.range (overlapInclusion W 1 2)) ⊆
      (integralCurveChart W 1) ⁻¹' closure (Set.range (integralCurveChart W 2)) := by
    apply closure_minimal _ (isClosed_closure.preimage (integralCurveChart W 1).continuous)
    rintro _ ⟨y, rfl⟩
    apply subset_closure
    refine ⟨Spec.map (CommRingCat.ofHom (transitionBase W 1 2).toRingHom) y, ?_⟩
    exact congrArg (fun f => f y) (integralCurve_output_transition W 1 2)
  exact h ((infinityOverlap_denseRange W) x)

/-- The original affine chart is dense in the entire glued cubic. -/
theorem integralCurveAffine_denseRange : DenseRange (integralCurveChart W 2) := by
  intro x
  rcases integralCurve_yz_cover W x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · exact infinityChart_subset_affine_closure W ⟨y, rfl⟩
  · exact subset_closure ⟨z, rfl⟩

end FLT.Mazur.WeierstrassIntegralChart
