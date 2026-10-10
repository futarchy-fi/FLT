/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationReesProjGluing
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# The fraction atlas embeds openly in the original Rees Proj

The full ratio preimage identifies every intersection point of the scale
and horizontal charts with a point of their actual gluing overlap. This
proves global injectivity; the chartwise open immersions then prove the
global map is an open immersion.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassModificationReesCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s : R)

instance scaleProjInclusion_isOpenImmersion : IsOpenImmersion (scaleProjInclusion W s) :=
  BlowupRees.fractionChartInclusion_isOpenImmersion _ _ _

instance horizontalProjInclusion_isOpenImmersion :
    IsOpenImmersion (horizontalProjInclusion W s) :=
  BlowupRees.fractionChartInclusion_isOpenImmersion _ _ _

/-- A horizontal point whose Proj image lies in the scale chart lies in the full ratio open. -/
theorem horizontal_mem_overlap_of_scale
    (x : Spec (.of (WeierstrassModificationX.horizontalReesChart W s)))
    (y : Spec (.of (WeierstrassDilatation.scaleReesChart W s)))
    (hxy : horizontalProjInclusion W s x = scaleProjInclusion W s y) :
    x ∈ Set.range (horizontalOpenInclusion W s) := by
  have hy : horizontalProjInclusion W s x ∈
      BlowupRees.generatorOpen (WeierstrassDilatation.modificationCenter W s)
        (algebraMap R (WeierstrassIntegralChart.Coordinate W 2) s)
        (Ideal.subset_span (by simp)) := by
    rw [← BlowupRees.fractionChartInclusion_range]
    exact ⟨y, hxy.symm⟩
  have hx : x ∈ BlowupRees.fractionChartInclusion
      (WeierstrassDilatation.modificationCenter W s)
      (WeierstrassIntegralChart.coord W 2 0) (Ideal.subset_span (by simp)) ⁻¹ᵁ
        BlowupRees.generatorOpen (WeierstrassDilatation.modificationCenter W s)
          (algebraMap R (WeierstrassIntegralChart.Coordinate W 2) s)
          (Ideal.subset_span (by simp)) := hy
  rw [BlowupRees.fractionChartInclusion_preimage] at hx
  change x ∈ Set.range (PrincipalAffineRefinement.inclusion (horizontalScale W s))
  rw [PrincipalAffineRefinement.range_inclusion]
  exact hx

variable [IsDomain R] (b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)

/-- Equal images from different charts already represent the same atlas point. -/
theorem horizontal_scale_eq_of_proj_eq
    (x : Spec (.of (WeierstrassModificationX.horizontalReesChart W s)))
    (y : Spec (.of (WeierstrassDilatation.scaleReesChart W s)))
    (hxy : horizontalProjInclusion W s x = scaleProjInclusion W s y) :
    horizontalChart W s b3 b4 b6 h3 h4 h6 hs x =
      scaleChart W s b3 b4 b6 h3 h4 h6 hs y := by
  obtain ⟨o, rfl⟩ := horizontal_mem_overlap_of_scale W s x y hxy
  have ho : horizontalOverlapToScale W s b3 b4 b6 h3 h4 h6 hs o = y := by
    apply (scaleProjInclusion W s).isOpenEmbedding.injective
    change (horizontalOverlapToScale W s b3 b4 b6 h3 h4 h6 hs ≫
      scaleProjInclusion W s) o = _
    rw [horizontalOverlap_toProj]
    exact hxy
  rw [← ho]
  exact congrArg (fun f => (f : Spec (.of (HorizontalScaleOpen W s)) ⟶ _) o)
    (fractionChart_overlap W s b3 b4 b6 h3 h4 h6 hs)

/-- The fraction atlas has no extra identifications under its original Proj map. -/
theorem fractionAtlasToProj_injective :
    Function.Injective (fractionAtlasToProj W s b3 b4 b6 h3 h4 h6 hs) := by
  intro x y hxy
  rcases fraction_charts_cover W s b3 b4 b6 h3 h4 h6 hs x with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases fraction_charts_cover W s b3 b4 b6 h3 h4 h6 hs y with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · change (horizontalChart W s b3 b4 b6 h3 h4 h6 hs ≫
      fractionAtlasToProj W s b3 b4 b6 h3 h4 h6 hs) a =
        (horizontalChart W s b3 b4 b6 h3 h4 h6 hs ≫
          fractionAtlasToProj W s b3 b4 b6 h3 h4 h6 hs) b at hxy
    rw [horizontalChart_toProj] at hxy
    exact congrArg _ ((horizontalProjInclusion W s).isOpenEmbedding.injective hxy)
  · change (horizontalChart W s b3 b4 b6 h3 h4 h6 hs ≫
      fractionAtlasToProj W s b3 b4 b6 h3 h4 h6 hs) a =
        (scaleChart W s b3 b4 b6 h3 h4 h6 hs ≫
          fractionAtlasToProj W s b3 b4 b6 h3 h4 h6 hs) b at hxy
    rw [horizontalChart_toProj, scaleChart_toProj] at hxy
    exact horizontal_scale_eq_of_proj_eq W s b3 b4 b6 h3 h4 h6 hs a b hxy
  · change (scaleChart W s b3 b4 b6 h3 h4 h6 hs ≫
      fractionAtlasToProj W s b3 b4 b6 h3 h4 h6 hs) a =
        (horizontalChart W s b3 b4 b6 h3 h4 h6 hs ≫
          fractionAtlasToProj W s b3 b4 b6 h3 h4 h6 hs) b at hxy
    rw [scaleChart_toProj, horizontalChart_toProj] at hxy
    exact (horizontal_scale_eq_of_proj_eq W s b3 b4 b6 h3 h4 h6 hs b a hxy.symm).symm
  · change (scaleChart W s b3 b4 b6 h3 h4 h6 hs ≫
      fractionAtlasToProj W s b3 b4 b6 h3 h4 h6 hs) a =
        (scaleChart W s b3 b4 b6 h3 h4 h6 hs ≫
          fractionAtlasToProj W s b3 b4 b6 h3 h4 h6 hs) b at hxy
    rw [scaleChart_toProj] at hxy
    exact congrArg _ ((scaleProjInclusion W s).isOpenEmbedding.injective hxy)

/-- The global fraction-atlas map is an open immersion, including its exceptional points. -/
instance fractionAtlasToProj_isOpenImmersion :
    IsOpenImmersion (fractionAtlasToProj W s b3 b4 b6 h3 h4 h6 hs) := by
  apply IsOpenImmersion.of_forall_source_exists _
    (fractionAtlasToProj_injective W s b3 b4 b6 h3 h4 h6 hs)
  intro x
  rcases fraction_charts_cover W s b3 b4 b6 h3 h4 h6 hs x with ⟨a, ha⟩ | ⟨a, ha⟩
  · refine ⟨_, horizontalChart W s b3 b4 b6 h3 h4 h6 hs, inferInstance, ⟨a, ha⟩, ?_⟩
    rw [horizontalChart_toProj]
    infer_instance
  · refine ⟨_, scaleChart W s b3 b4 b6 h3 h4 h6 hs, inferInstance, ⟨a, ha⟩, ?_⟩
    rw [scaleChart_toProj]
    infer_instance

end FLT.Mazur.WeierstrassModificationReesCoordinates
