/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveReesProjGluing
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

namespace FLT.Mazur.WeierstrassSuccessiveRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)

local notation "B" =>
  WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "BX" => WeierstrassDilatation.x W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "I" => WeierstrassSuccessiveX.modificationCenter W s π b3 b4 b6

instance scaleProjInclusion_isOpenImmersion : IsOpenImmersion (scaleProjInclusion W s π b3 b4 b6) :=
  BlowupRees.fractionChartInclusion_isOpenImmersion _ _ _

instance horizontalProjInclusion_isOpenImmersion :
    IsOpenImmersion (horizontalProjInclusion W s π b3 b4 b6) :=
  BlowupRees.fractionChartInclusion_isOpenImmersion _ _ _

/-- A horizontal point whose Proj image lies in the scale chart lies in the full ratio open. -/
theorem horizontal_mem_overlap_of_scale
    (x : Spec (.of (WeierstrassSuccessiveX.horizontalReesChart W s π b3 b4 b6)))
    (y : Spec (.of (WeierstrassSuccessiveScale.scaleReesChart W s π b3 b4 b6)))
    (hxy : horizontalProjInclusion W s π b3 b4 b6 x = scaleProjInclusion W s π b3 b4 b6 y) :
    x ∈ Set.range (horizontalOpenInclusion W s π b3 b4 b6) := by
  have hy : horizontalProjInclusion W s π b3 b4 b6 x ∈
      BlowupRees.generatorOpen I
        (algebraMap R B π)
        (Ideal.subset_span (by simp)) := by
    rw [← BlowupRees.fractionChartInclusion_range]
    exact ⟨y, hxy.symm⟩
  have hx : x ∈ BlowupRees.fractionChartInclusion
      I
      BX (Ideal.subset_span (by simp)) ⁻¹ᵁ
        BlowupRees.generatorOpen I
          (algebraMap R B π)
          (Ideal.subset_span (by simp)) := hy
  rw [BlowupRees.fractionChartInclusion_preimage] at hx
  change x ∈ Set.range (PrincipalAffineRefinement.inclusion (horizontalScale W s π b3 b4 b6))
  rw [PrincipalAffineRefinement.range_inclusion]
  exact hx

variable [IsDomain R] (hπ : π ≠ 0)

/-- Equal images from different charts already represent the same atlas point. -/
theorem horizontal_scale_eq_of_proj_eq
    (x : Spec (.of (WeierstrassSuccessiveX.horizontalReesChart W s π b3 b4 b6)))
    (y : Spec (.of (WeierstrassSuccessiveScale.scaleReesChart W s π b3 b4 b6)))
    (hxy : horizontalProjInclusion W s π b3 b4 b6 x = scaleProjInclusion W s π b3 b4 b6 y) :
    horizontalChart W s π b3 b4 b6 hπ x =
      scaleChart W s π b3 b4 b6 hπ y := by
  obtain ⟨o, rfl⟩ := horizontal_mem_overlap_of_scale W s π b3 b4 b6 x y hxy
  have ho : horizontalOverlapToScale W s π b3 b4 b6 hπ o = y := by
    apply (scaleProjInclusion W s π b3 b4 b6).isOpenEmbedding.injective
    change (horizontalOverlapToScale W s π b3 b4 b6 hπ ≫
      scaleProjInclusion W s π b3 b4 b6) o = _
    rw [horizontalOverlap_toProj]
    exact hxy
  rw [← ho]
  exact congrArg (fun f => (f : Spec (.of (HorizontalScaleOpen W s π b3 b4 b6)) ⟶ _) o)
    (fractionChart_overlap W s π b3 b4 b6 hπ)

/-- The fraction atlas has no extra identifications under its original Proj map. -/
theorem fractionAtlasToProj_injective :
    Function.Injective (fractionAtlasToProj W s π b3 b4 b6 hπ) := by
  intro x y hxy
  rcases fractionAtlas_charts_cover W s π b3 b4 b6 hπ x with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases fractionAtlas_charts_cover W s π b3 b4 b6 hπ y with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · change (horizontalChart W s π b3 b4 b6 hπ ≫
      fractionAtlasToProj W s π b3 b4 b6 hπ) a =
        (horizontalChart W s π b3 b4 b6 hπ ≫
          fractionAtlasToProj W s π b3 b4 b6 hπ) b at hxy
    rw [horizontalChart_toProj] at hxy
    exact congrArg _ ((horizontalProjInclusion W s π b3 b4 b6).isOpenEmbedding.injective hxy)
  · change (horizontalChart W s π b3 b4 b6 hπ ≫
      fractionAtlasToProj W s π b3 b4 b6 hπ) a =
        (scaleChart W s π b3 b4 b6 hπ ≫
          fractionAtlasToProj W s π b3 b4 b6 hπ) b at hxy
    rw [horizontalChart_toProj, scaleChart_toProj] at hxy
    exact horizontal_scale_eq_of_proj_eq W s π b3 b4 b6 hπ a b hxy
  · change (scaleChart W s π b3 b4 b6 hπ ≫
      fractionAtlasToProj W s π b3 b4 b6 hπ) a =
        (horizontalChart W s π b3 b4 b6 hπ ≫
          fractionAtlasToProj W s π b3 b4 b6 hπ) b at hxy
    rw [scaleChart_toProj, horizontalChart_toProj] at hxy
    exact (horizontal_scale_eq_of_proj_eq W s π b3 b4 b6 hπ b a hxy.symm).symm
  · change (scaleChart W s π b3 b4 b6 hπ ≫
      fractionAtlasToProj W s π b3 b4 b6 hπ) a =
        (scaleChart W s π b3 b4 b6 hπ ≫
          fractionAtlasToProj W s π b3 b4 b6 hπ) b at hxy
    rw [scaleChart_toProj] at hxy
    exact congrArg _ ((scaleProjInclusion W s π b3 b4 b6).isOpenEmbedding.injective hxy)

/-- The global fraction-atlas map is an open immersion, including its exceptional points. -/
instance fractionAtlasToProj_isOpenImmersion :
    IsOpenImmersion (fractionAtlasToProj W s π b3 b4 b6 hπ) := by
  apply IsOpenImmersion.of_forall_source_exists _
    (fractionAtlasToProj_injective W s π b3 b4 b6 hπ)
  intro x
  rcases fractionAtlas_charts_cover W s π b3 b4 b6 hπ x with ⟨a, ha⟩ | ⟨a, ha⟩
  · refine ⟨_, horizontalChart W s π b3 b4 b6 hπ, inferInstance, ⟨a, ha⟩, ?_⟩
    rw [horizontalChart_toProj]
    infer_instance
  · refine ⟨_, scaleChart W s π b3 b4 b6 hπ, inferInstance, ⟨a, ha⟩, ?_⟩
    rw [scaleChart_toProj]
    infer_instance

end FLT.Mazur.WeierstrassSuccessiveRees
