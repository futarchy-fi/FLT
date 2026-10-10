/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingMarkedSection
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Smoothness of the original node chart at a unit parameter

When the parameter is invertible, its original first punctured branch is
already the full affine smoothing chart. The original structure map is smooth.
This is a statement about the local model, not an open embedding into a proper fiber.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonSmoothing

variable (R : Type*) [CommRing R]

/-- A unit smoothing parameter makes the original left coordinate invertible. -/
theorem leftCoordinate_isUnit {t : R} (ht : IsUnit t) : IsUnit (leftCoordinate t) := by
  apply isUnit_of_mul_isUnit_left (y := rightCoordinate t)
  rw [coordinate_relation]
  exact ht.map (algebraMap R (ChartRing t))

/-- Every point of a unit-parameter chart belongs to the original left punctured branch. -/
theorem leftBranchOpen_surjective {t : R} (ht : IsUnit t) :
    Function.Surjective (leftBranchOpen R t) := by
  intro x
  have hx : x ∈ Set.range (leftBranchOpen R t) := by
    rw [leftBranchOpen_range]
    let _ := x.isPrime
    exact x.asIdeal.notMem_of_isUnit (leftCoordinate_isUnit R ht)
  exact hx

/-- The original branch inclusion is an isomorphism when the parameter is a unit. -/
theorem leftBranchOpen_isIso {t : R} (ht : IsUnit t) : IsIso (leftBranchOpen R t) := by
  apply (isIso_iff_isOpenImmersion_and_surjective _).mpr
  exact ⟨inferInstance, ⟨leftBranchOpen_surjective R ht⟩⟩

/-- The full original smoothing chart is smooth over its unit-parameter base. -/
theorem chartStructure_smooth_of_isUnit {t : R} (ht : IsUnit t) :
    Smooth (chartStructure R t) := by
  let _ := leftBranchOpen_isIso R ht
  have he : chartStructure R t =
      inv (leftBranchOpen R t) ≫ (leftBranchOpen R t ≫ chartStructure R t) := by simp
  rw [he]
  infer_instance

end FLT.Mazur.PolygonSmoothing
