/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingBranchOpens

/-!
# Specialization retains the original split-node branch maps

The zero-parameter comparison carries both new punctured branch immersions
to the original node's specified Laurent immersions, with their coordinates.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial

namespace FLT.Mazur.PolygonSmoothing

variable (R : Type*) [CommRing R]

/-- The original node's first Laurent restriction, as an algebra map. -/
def specialLeftMap : PolygonNodeEqualizer.A (R := R) →ₐ[R] R[T;T⁻¹] where
  __ := PolygonNodeLocalization.leftMap
  commutes' r := by
    change Polynomial.toLaurent (PolygonNodeEqualizer.first (algebraMap R _ r)) = _
    rw [AlgHom.commutes]
    exact Polynomial.toLaurent_C r

/-- The original node's second Laurent restriction, as an algebra map. -/
def specialRightMap : PolygonNodeEqualizer.A (R := R) →ₐ[R] R[T;T⁻¹] where
  __ := PolygonNodeLocalization.rightMap
  commutes' r := by
    change Polynomial.toLaurent (PolygonNodeEqualizer.second (algebraMap R _ r)) = _
    rw [AlgHom.commutes]
    exact Polynomial.toLaurent_C r

/-- The first specialized Laurent presentation is exactly the original restriction. -/
theorem specialLeftMap_comparison :
    (specialLeftMap R).comp (specialFiberEquiv R).toAlgHom = leftLaurentMap (0 : R) := by
  apply chartRing_hom_ext (0 : R)
  · change specialLeftMap R (specialFiberEquiv R (leftCoordinate 0)) = _
    rw [specialFiberEquiv_left, leftLaurentMap_left]
    exact PolygonNodeLocalization.leftMap_x
  · change specialLeftMap R (specialFiberEquiv R (rightCoordinate 0)) = _
    rw [specialFiberEquiv_right, leftLaurentMap_right, map_zero, zero_mul]
    exact PolygonNodeLocalization.leftMap_y

/-- The second specialized Laurent presentation is exactly the original restriction. -/
theorem specialRightMap_comparison :
    (specialRightMap R).comp (specialFiberEquiv R).toAlgHom =
      (leftLaurentMap (0 : R)).comp (branchSwapMap (0 : R)) := by
  apply chartRing_hom_ext (0 : R)
  · change specialRightMap R (specialFiberEquiv R (leftCoordinate 0)) =
      leftLaurentMap 0 (branchSwapMap 0 (leftCoordinate 0))
    rw [specialFiberEquiv_left, branchSwapMap_left, leftLaurentMap_right, map_zero, zero_mul]
    exact PolygonNodeLocalization.rightMap_x
  · change specialRightMap R (specialFiberEquiv R (rightCoordinate 0)) =
      leftLaurentMap 0 (branchSwapMap 0 (rightCoordinate 0))
    rw [specialFiberEquiv_right, branchSwapMap_right, leftLaurentMap_left]
    exact PolygonNodeLocalization.rightMap_y

/-- The first actual punctured branch specializes to the original first node immersion. -/
@[reassoc] theorem specialFiberIso_left :
    PolygonNodeBranches.left R ≫ (specialFiberIso R).hom = leftBranchOpen R 0 := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change specialLeftMap R (specialFiberEquiv R z) =
    leftPunctureToLaurent 0 (algebraMap (ChartRing (0 : R)) _ z)
  rw [leftPunctureToLaurent_map]
  exact DFunLike.congr_fun (specialLeftMap_comparison R) z

/-- The second actual punctured branch specializes to the original second node immersion. -/
@[reassoc] theorem specialFiberIso_right :
    PolygonNodeBranches.right R ≫ (specialFiberIso R).hom = rightBranchOpen R 0 := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change specialRightMap R (specialFiberEquiv R z) =
    leftPunctureToLaurent 0 (rightToLeftPuncture 0 (algebraMap (ChartRing (0 : R)) _ z))
  rw [rightToLeftPuncture_map, leftPunctureToLaurent_map]
  exact DFunLike.congr_fun (specialRightMap_comparison R) z

end FLT.Mazur.PolygonSmoothing
