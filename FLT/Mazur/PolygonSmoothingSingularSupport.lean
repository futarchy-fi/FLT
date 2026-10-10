/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingMarkedSection

/-!
# Support of nonsmooth points in the original smoothing model

Both punctured branches are smooth over the original base. Consequently a
nonsmooth point contains both original coordinates and the smoothing parameter.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonSmoothing

variable (R : Type*) [CommRing R] (t : R)

/-- Every point on the original first punctured branch is smooth over the base. -/
theorem leftBranchOpen_mem_smoothLocus (x : branchTorus R) :
    leftBranchOpen R t x ∈ (chartStructure R t).smoothLocus := by
  have hx : x ∈ (leftBranchOpen R t ≫ chartStructure R t).smoothLocus := by
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  rwa [← Scheme.Hom.preimage_smoothLocus_eq] at hx

/-- Every point on the original second punctured branch is smooth over the base. -/
theorem rightBranchOpen_mem_smoothLocus (x : branchTorus R) :
    rightBranchOpen R t x ∈ (chartStructure R t).smoothLocus := by
  have hx : x ∈ (rightBranchOpen R t ≫ chartStructure R t).smoothLocus := by
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  rwa [← Scheme.Hom.preimage_smoothLocus_eq] at hx

/-- At a nonsmooth point, both original branch coordinates vanish in the residue field. -/
theorem coordinates_mem_of_not_smooth (x : chart R t)
    (hx : x ∉ (chartStructure R t).smoothLocus) :
    leftCoordinate t ∈ x.asIdeal ∧ rightCoordinate t ∈ x.asIdeal := by
  constructor
  · by_contra hn
    have hm : x ∈ Set.range (leftBranchOpen R t) := by
      rw [leftBranchOpen_range]
      exact hn
    obtain ⟨y, rfl⟩ := hm
    exact hx (leftBranchOpen_mem_smoothLocus R t y)
  · by_contra hn
    have hm : x ∈ Set.range (rightBranchOpen R t) := by
      rw [rightBranchOpen_range]
      exact hn
    obtain ⟨y, rfl⟩ := hm
    exact hx (rightBranchOpen_mem_smoothLocus R t y)

/-- All nonsmooth points of the arithmetic node model lie over the zero parameter. -/
theorem parameter_mem_of_not_smooth (x : chart R t)
    (hx : x ∉ (chartStructure R t).smoothLocus) :
    t ∈ (chartStructure R t x).asIdeal := by
  change algebraMap R (ChartRing t) t ∈ x.asIdeal
  rw [← coordinate_relation]
  exact x.asIdeal.mul_mem_right _ (coordinates_mem_of_not_smooth R t x hx).1

/-- The inverse image of the punctured parameter base is contained in the smooth locus. -/
theorem parameterOpen_le_smoothLocus :
    chartStructure R t ⁻¹ᵁ PrimeSpectrum.basicOpen t ≤ (chartStructure R t).smoothLocus := by
  intro x hx
  by_contra hn
  exact hx (parameter_mem_of_not_smooth R t x hn)

end FLT.Mazur.PolygonSmoothing
