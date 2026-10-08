/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralProjectiveMap
public import FLT.Mazur.ProjectiveChartPointMembership

/-!
# Inverse images of projective charts on the integral cubic

The projective morphism pulls each ambient coordinate open back to exactly
the corresponding normalized cubic chart. A nonvanishing coordinate lifts
to the concrete principal overlap, whose transition gives the new chart.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The target coordinate open tests nonvanishing of the corresponding cubic coordinate. -/
theorem projectiveChartMap_mem_iff (j k : Fin 3) (x : chartScheme W j) :
    projectiveChartMap W j x ∈ ProjectiveSpace.chart R (Fin 3) k ↔
      coord W j k ∉ x.asIdeal := by
  change x ∈ (projectiveChartMorphism W j ≫ ProjectiveSpace.chartMap R (Fin 3) j) ⁻¹ᵁ
    ProjectiveSpace.chart R (Fin 3) k ↔ _
  rw [Scheme.Hom.comp_preimage, ProjectiveSpace.chartMap_preimage_chart]
  change x ∈ Spec.map (CommRingCat.ofHom (projectiveChartAlgebra W j).toRingHom) ⁻¹ᵁ
    PrimeSpectrum.basicOpen (ProjectiveSpace.coordinate R (Fin 3) j k) ↔ _
  rw [SpecMap_preimage_basicOpen]
  change projectiveChartAlgebra W j (ProjectiveSpace.coordinate R (Fin 3) j k) ∉ x.asIdeal ↔ _
  rw [projectiveChartAlgebra_coordinate]

/-- A nonvanishing coordinate moves an actual scheme point into that normalized chart. -/
theorem integralCurveChart_mem_range (j k : Fin 3) (x : chartScheme W j)
    (hx : coord W j k ∉ x.asIdeal) :
    integralCurveChart W j x ∈ Set.range (integralCurveChart W k) := by
  have hx' : x ∈ Set.range (overlapInclusion W j k) := by
    rw [overlapInclusion, PrincipalAffineRefinement.range_inclusion]
    exact hx
  obtain ⟨y, rfl⟩ := hx'
  refine ⟨(chartTransition W j k ≫ overlapInclusion W k j) y, ?_⟩
  exact congrArg (fun f : overlapScheme W j k ⟶ integralCurve W => f y)
    (integralCurveChart_compatibility W j k)

/-- Each projective standard open pulls back to precisely the matching integral chart. -/
theorem integralProjectiveMap_preimage_chart (j : Fin 3) :
    integralProjectiveMap W ⁻¹ᵁ ProjectiveSpace.chart R (Fin 3) j =
      (integralCurveChart W j).opensRange := by
  ext x
  change integralProjectiveMap W x ∈ ProjectiveSpace.chart R (Fin 3) j ↔
    x ∈ Set.range (integralCurveChart W j)
  constructor
  · intro hx
    obtain ⟨k, y, rfl⟩ := integralCurveChart_cover W x
    have hy : projectiveChartMap W k y ∈ ProjectiveSpace.chart R (Fin 3) j := by
      rw [← integralCurveChart_projectiveMap]
      exact hx
    exact integralCurveChart_mem_range W k j y ((projectiveChartMap_mem_iff W k j y).mp hy)
  · rintro ⟨y, rfl⟩
    change (integralCurveChart W j ≫ integralProjectiveMap W) y ∈ _
    rw [integralCurveChart_projectiveMap, projectiveChartMap_mem_iff, coord_self]
    exact y.asIdeal.one_notMem

end FLT.Mazur.WeierstrassIntegralChart
