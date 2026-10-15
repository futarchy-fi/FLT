/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstNodeTangentEquiv
public import FLT.Mazur.PolygonFirstNodeBoundary
public import FLT.Mazur.PolygonFirstOrderCoordinateCharts

/-!
# Exact Laurent restriction of the constructed first-node lift

Lifting a split-node derivation produces the first-order coordinate of its
actual branch polynomial. This retains every coefficient over the original
nonreduced smoothing base, and identifies the previously extracted boundary
polynomial with the vector field used in the construction.
-/

@[expose] public noncomputable section
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing PolygonNodeEqualizer LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R]
local notation "S" => Ring R 1
local notation "e" => parameter R 1
local notation "N" => ChartRing (0 : R)

/-- Extraction after lifting returns the original first branch polynomial exactly. -/
theorem firstNodeTangentLift_boundaryField (d : Derivation R (N) (N)) :
    firstNodeBoundaryField R (firstNodeTangentLift R d) (firstNodeTangentLift_reduction R d) =
      first (specialFiberEquiv R (d (leftCoordinate (0 : R)))) := by
  have he := congrArg (fun D : Derivation R (N) (N) ↦
    first (specialFiberEquiv R (D (leftCoordinate (0 : R)))))
    (firstNodeTangentLift_derivation R d)
  simpa only [firstNodeDifferenceDerivation, derivationOfCoordinates_left,
    firstNodeBoundaryField] using he

/-- The constructed full boundary polynomial has the original vector field as its coefficient. -/
theorem firstNodeTangentLift_boundaryPolynomial (d : Derivation R (N) (N)) :
    firstNodeBoundaryPolynomial R (firstNodeTangentLift R d)
        (firstNodeTangentLift_reduction R d) =
      Polynomial.X + Polynomial.C (e) *
        (first (specialFiberEquiv R (d (leftCoordinate (0 : R))))).map
          (algebraMap R (S)) := by
  rw [firstNodeBoundaryPolynomial, firstNodeTangentLift_boundaryField]

/-- Restriction of the actual lift is the complete first-order Laurent coordinate. -/
theorem firstNodeTangentLift_leftLaurent (d : Derivation R (N) (N)) :
    leftLaurentMap (e) (firstNodeTangentLift R d (leftCoordinate (e))) =
      firstOrderLaurentCoordinate
        (first (specialFiberEquiv R (d (leftCoordinate (0 : R))))).toLaurent := by
  rw [← firstNodeBoundaryPolynomial_toLaurent R (firstNodeTangentLift R d)
    (firstNodeTangentLift_reduction R d), firstNodeTangentLift_boundaryPolynomial]
  simp only [map_add, map_mul, Polynomial.toLaurent_X, Polynomial.toLaurent_C,
    firstOrderLaurentCoordinate]
  congr 2
  exact (RingHom.congr_fun (PolygonScalingNaturality.coeffMap_toLaurent
    (algebraMap R (S))) _).symm

/-- The original coordinate unit is realized whenever its field is this actual branch field. -/
theorem firstNodeTangentLift_coordinateUnit (d : Derivation R (N) (N)) :
    leftLaurentMap (e) (firstNodeTangentLift R d (leftCoordinate (e))) =
      (firstOrderCoordinateUnit
        (first (specialFiberEquiv R (d (leftCoordinate (0 : R))))).toLaurent).val := by
  rw [firstOrderCoordinateUnit_val, firstNodeTangentLift_leftLaurent]

end FLT.Mazur.PolygonInfinitesimalStages
