/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginIdealSheaf

/-!
# The intrinsic origin ideal on the original affine chart

The original affine chart is disjoint from the actual zero section, so the
origin ideal and all its powers restrict there to the unit ideal.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- No point of the actual origin section lies in the original affine chart. -/
theorem originSection_notMem_affine (x : Spec (.of R)) :
    integralCurveZero W x ∉ Set.range (integralCurveChart W 2) := by
  intro hx
  let y := Spec.map (CommRingCat.ofHom
    (chartInfinityEvaluation (S := R) W).toRingHom) x
  have hy : integralCurveChart W 1 y = integralCurveZero W x := rfl
  have hi : integralCurveZero W x ∈
      Set.range (overlapInclusion W 1 2 ≫ integralCurveChart W 1) := by
    rw [integralChartIntersection_range]
    exact ⟨⟨y, hy⟩, hx⟩
  obtain ⟨z, hz⟩ := hi
  have he : overlapInclusion W 1 2 z = y :=
    (integralCurveChart W 1).isOpenEmbedding.injective (hz.trans hy.symm)
  have hm : y ∈ Set.range (overlapInclusion W 1 2) := ⟨z, he⟩
  rw [overlapInclusion, PrincipalAffineRefinement.range_inclusion] at hm
  change chartInfinityEvaluation (S := R) W (coord W 1 2) ∉ x.asIdeal at hm
  exact hm (by simp)

/-- The intrinsic origin ideal is the unit ideal on the actual affine chart. -/
theorem originIdealSheaf_affine :
    (integralCurveZero W).ker.comap (integralCurveChart W 2) = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  rw [Scheme.IdealSheafData.support_comap]
  apply TopologicalSpace.Closeds.ext
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  change integralCurveChart W 2 x ∈
    ((integralCurveZero W).ker.support : Set (integralCurve W)) at hx
  rw [Scheme.Hom.support_ker,
    (integralCurveZero W).isClosedEmbedding.isClosed_range.closure_eq] at hx
  obtain ⟨y, hy⟩ := hx
  exact originSection_notMem_affine W y ⟨x, hy.symm⟩

/-- All powers of the origin ideal have the unit equation on the original affine chart. -/
theorem originIdealSheaf_power_affine (n : ℕ) :
    ((integralCurveZero W).ker ^ n).comap (integralCurveChart W 2) = ⊤ := by
  rw [FCurve.idealSheaf_comap_pow, originIdealSheaf_affine]
  exact one_pow n

end FLT.Mazur.WeierstrassIntegralChart
