/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationYDescent
public import FLT.Mazur.WeierstrassModificationChartIntersection
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# The descended y-chart is an open immersion

A collision between the two local y-chart maps lies in the x/divided
principal overlap. Its incidence coordinate r/u is invertible, forcing the
horizontal-cover point into the scale open as well. Local injectivity then
proves global injectivity, and the local open immersions descend.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassModificationY

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- A horizontal-cover point meeting the divided chart also lies in the scale open. -/
theorem horizontal_mem_scale_of_meets_divided
    (q : Spec (.of (HorizontalOpen W s b3 b4 b6)))
    (h : horizontalToModification W s b3 b4 b6 q ∈
      Set.range (WeierstrassModificationX.dividedChart W s b3 b4 b6)) :
    PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 1) q ∈
      Set.range (PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 0)) := by
  have ht := WeierstrassModificationX.xChart_mem_dividedChart W s b3 b4 b6
    (horizontalToX W s b3 b4 b6 q) h
  rw [horizontalToX_eq] at ht
  change toX W s b3 b4 b6 (IsScalarTower.toAlgHom R _ _)
    (horizontalUnit W s b3 b4 b6) (horizontalUnit_val W s b3 b4 b6).symm
    (WeierstrassModificationX.t W s b3 b4 b6) ∉ q.asIdeal at ht
  rw [toX_t] at ht
  rw [PrincipalAffineRefinement.range_inclusion]
  change algebraMap _ (HorizontalOpen W s b3 b4 b6) (coord W s b3 b4 b6 0) ∉ q.asIdeal
  intro hr
  exact ht (q.asIdeal.mul_mem_right _ hr)

/-- Equal images of points in different y-cover members have the same original y-chart point. -/
theorem ratioChart_collision
    (p : Spec (.of (ScaleOpen W s b3 b4 b6)))
    (q : Spec (.of (HorizontalOpen W s b3 b4 b6)))
    (h : scaleToModification W s b3 b4 b6 p = horizontalToModification W s b3 b4 b6 q) :
    PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 0) p =
      PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 1) q := by
  obtain ⟨p', hp'⟩ := horizontal_mem_scale_of_meets_divided W s b3 b4 b6 q
    ⟨scaleToDivided W s b3 b4 b6 p, h⟩
  have hs : scaleToModification W s b3 b4 b6 p' =
      horizontalToModification W s b3 b4 b6 q := by
    rw [← scale_yChart, ← horizontal_yChart]
    change yChart W s b3 b4 b6
      (PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 0) p') =
        yChart W s b3 b4 b6
          (PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 1) q)
    exact congrArg _ hp'
  have hp := (scaleToModification W s b3 b4 b6).isOpenEmbedding.injective (h.trans hs.symm)
  exact (congrArg (PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 0)) hp).trans hp'

/-- Every y-chart point has a representative in one of the two actual ratio opens. -/
theorem ratio_points_cover (z : Spec (.of (Coordinate W s b3 b4 b6))) :
    (∃ p, PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 0) p = z) ∨
      ∃ q, PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 1) q = z := by
  obtain ⟨i, hi⟩ := ratio_exists_not_mem W s b3 b4 b6 z
  fin_cases i
  · left
    change z ∈ Set.range (PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 0))
    rw [PrincipalAffineRefinement.range_inclusion]
    exact hi
  · right
    change z ∈ Set.range (PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 1))
    rw [PrincipalAffineRefinement.range_inclusion]
    exact hi

/-- The descended whole-chart morphism is injective on its actual topological space. -/
theorem yChart_injective : Function.Injective (yChart W s b3 b4 b6) := by
  intro x y h
  rcases ratio_points_cover W s b3 b4 b6 x with ⟨p, rfl⟩ | ⟨p, rfl⟩ <;>
    rcases ratio_points_cover W s b3 b4 b6 y with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · have he : scaleToModification W s b3 b4 b6 p = scaleToModification W s b3 b4 b6 q := by
      simpa only [← Scheme.Hom.comp_apply, scale_yChart] using h
    exact congrArg _ ((scaleToModification W s b3 b4 b6).isOpenEmbedding.injective he)
  · apply ratioChart_collision W s b3 b4 b6
    simpa only [← Scheme.Hom.comp_apply, scale_yChart, horizontal_yChart] using h
  · apply Eq.symm
    apply ratioChart_collision W s b3 b4 b6
    simpa only [← Scheme.Hom.comp_apply, scale_yChart, horizontal_yChart] using h.symm
  · have he : horizontalToModification W s b3 b4 b6 p =
        horizontalToModification W s b3 b4 b6 q := by
      simpa only [← Scheme.Hom.comp_apply, horizontal_yChart] using h
    exact congrArg _ ((horizontalToModification W s b3 b4 b6).isOpenEmbedding.injective he)

/-- The actual y-direction chart embeds openly into the glued modification. -/
instance yChart_isOpenImmersion : IsOpenImmersion (yChart W s b3 b4 b6) := by
  apply IsOpenImmersion.of_openCover_source _ (ratioCover W s b3 b4 b6)
    (yChart_injective W s b3 b4 b6)
  intro i
  change Fin 2 at i
  rw [ratioCover_yChart]
  fin_cases i
  · exact scaleToModification_isOpenImmersion W s b3 b4 b6
  · exact horizontalToModification_isOpenImmersion W s b3 b4 b6

end FLT.Mazur.WeierstrassModificationY
