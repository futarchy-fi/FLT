/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonTopNodeTangentEquiv
public import FLT.Mazur.PolygonTopNodeBoundary
public import FLT.Mazur.PolygonTopOrderCoordinateCharts

/-!
# Exact Laurent restriction of the constructed top-layer node lift

Lifting a split-node derivation produces the top-weight coordinate of its
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
variable (R : Type) [CommRing R] (m : ℕ)
local notation "S" => Ring R (m + 1)
local notation "e" => parameter R (m + 1)
local notation "N" => ChartRing (0 : R)

/-- Extraction after lifting returns the original first branch polynomial exactly. -/
theorem topNodeTangentLift_boundaryField (d : Derivation R (N) (N)) :
    topNodeBoundaryField R m (topNodeTangentLift R m d) (topNodeTangentLift_restriction R m d) =
      first (specialFiberEquiv R (d (leftCoordinate (0 : R)))) := by
  have he := congrArg (fun D : Derivation R (N) (N) ↦
    first (specialFiberEquiv R (D (leftCoordinate (0 : R)))))
    (topNodeTangentLift_derivation R m d)
  simpa only [topNodeDifferenceDerivation, derivationOfCoordinates_left,
    topNodeBoundaryField] using he

/-- The constructed full boundary polynomial has the original vector field as its coefficient. -/
theorem topNodeTangentLift_boundaryPolynomial (d : Derivation R (N) (N)) :
    topNodeBoundaryPolynomial R m (topNodeTangentLift R m d)
        (topNodeTangentLift_restriction R m d) =
      Polynomial.X + Polynomial.C ((e) ^ (m + 1)) *
        (first (specialFiberEquiv R (d (leftCoordinate (0 : R))))).map
          (algebraMap R (S)) := by
  rw [topNodeBoundaryPolynomial, topNodeTangentLift_boundaryField]

/-- Restriction of the actual lift is the complete top-weight Laurent coordinate. -/
theorem topNodeTangentLift_leftLaurent (d : Derivation R (N) (N)) :
    leftLaurentMap (e) (topNodeTangentLift R m d (leftCoordinate (e))) =
      topOrderLaurentCoordinate (m + 1)
        (first (specialFiberEquiv R (d (leftCoordinate (0 : R))))).toLaurent := by
  rw [← topNodeBoundaryPolynomial_toLaurent R m (topNodeTangentLift R m d)
    (topNodeTangentLift_restriction R m d), topNodeTangentLift_boundaryPolynomial]
  simp only [map_add, map_mul, Polynomial.toLaurent_X, Polynomial.toLaurent_C,
    topOrderLaurentCoordinate]
  congr 2
  exact (RingHom.congr_fun (PolygonScalingNaturality.coeffMap_toLaurent
    (algebraMap R (S))) _).symm

/-- The original coordinate unit is realized whenever its field is this actual branch field. -/
theorem topNodeTangentLift_coordinateUnit (d : Derivation R (N) (N)) :
    leftLaurentMap (e) (topNodeTangentLift R m d (leftCoordinate (e))) =
      (topOrderCoordinateUnit m
        (first (specialFiberEquiv R (d (leftCoordinate (0 : R))))).toLaurent).val := by
  rw [topOrderCoordinateUnit_val, topNodeTangentLift_leftLaurent]

end FLT.Mazur.PolygonInfinitesimalStages
