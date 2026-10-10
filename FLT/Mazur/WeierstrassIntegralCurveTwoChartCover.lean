/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralCurveMorphisms

/-!
# The two-chart cover of the integral cubic

On the chart X = 1 the Weierstrass equation makes Z a unit, so this whole chart
lies in the affine Z-chart. Consequently the Y- and Z-charts cover the glued
curve over every commutative ring, without a discriminant assumption.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- On X = 1 the cubic equation explicitly makes Z invertible. -/
theorem xChart_z_isUnit : IsUnit (coord W 0 2) := by
  let E := W.map (algebraMap R (Coordinate W 0))
  let y := coord W 0 1
  let z := coord W 0 2
  have h := (E.toProjective.equation_iff (coord W 0)).mp (coord_equation W 0)
  change y ^ 2 * z + E.a₁ * coord W 0 0 * y * z + E.a₃ * y * z ^ 2 -
    (coord W 0 0 ^ 3 + E.a₂ * coord W 0 0 ^ 2 * z +
      E.a₄ * coord W 0 0 * z ^ 2 + E.a₆ * z ^ 3) = 0 at h
  rw [coord_self] at h
  refine isUnit_iff_exists_inv.mpr ⟨y ^ 2 + E.a₁ * y + E.a₃ * y * z -
    E.a₂ - E.a₄ * z - E.a₆ * z ^ 2, ?_⟩
  change z * _ = 1
  calc
    _ = 1 + (y ^ 2 * z + E.a₁ * 1 * y * z + E.a₃ * y * z ^ 2 -
      (1 ^ 3 + E.a₂ * 1 ^ 2 * z + E.a₄ * 1 * z ^ 2 + E.a₆ * z ^ 3)) := by ring
    _ = 1 := by rw [h, add_zero]

/-- The overlap of the X-chart with the affine chart is the entire X-chart. -/
instance xChart_affineOverlap_isIso : IsIso (overlapInclusion W 0 2) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply TopologicalSpace.Opens.ext
  change Set.range (PrincipalAffineRefinement.inclusion (coord W 0 2)) = Set.univ
  rw [PrincipalAffineRefinement.range_inclusion]
  apply Set.eq_univ_of_forall
  intro p
  exact p.asIdeal.notMem_of_isUnit (xChart_z_isUnit W)

/-- The redundant X-chart factors through the affine chart. -/
def xChartToAffine : chartScheme W 0 ⟶ chartScheme W 2 :=
  inv (overlapInclusion W 0 2) ≫
    Spec.map (CommRingCat.ofHom (transitionBase W 0 2).toRingHom)

/-- The factorization is the original chart inclusion into the glued curve. -/
theorem xChartToAffine_inclusion :
    xChartToAffine W ≫ integralCurveChart W 2 = integralCurveChart W 0 := by
  rw [xChartToAffine, Category.assoc, integralCurve_output_transition,
    IsIso.inv_hom_id_assoc]

/-- The two charts used by all existing addition covers already cover the curve. -/
theorem integralCurve_yz_cover (x : integralCurve W) :
    (∃ y : chartScheme W 1, integralCurveChart W 1 y = x) ∨
      (∃ z : chartScheme W 2, integralCurveChart W 2 z = x) := by
  obtain ⟨j, y, rfl⟩ := integralCurveChart_cover W x
  fin_cases j
  · right
    exact ⟨xChartToAffine W y, congrArg (fun f => f y) (xChartToAffine_inclusion W)⟩
  · exact Or.inl ⟨y, rfl⟩
  · exact Or.inr ⟨y, rfl⟩

/-- The Y/Z affine atlas as an actual scheme open cover. -/
def integralCurveTwoChartCover : (integralCurve W).OpenCover where
  I₀ := Bool
  X b := chartScheme W (if b then 1 else 2)
  f b := integralCurveChart W (if b then 1 else 2)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun _ => inferInstance⟩
    intro x
    rcases integralCurve_yz_cover W x with ⟨y, hy⟩ | ⟨z, hz⟩
    · exact ⟨true, y, hy⟩
    · exact ⟨false, z, hz⟩

end FLT.Mazur.WeierstrassIntegralChart
