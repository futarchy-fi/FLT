/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXResidueInfinityBoundary
public import FLT.Mazur.WeierstrassModificationXFiberExteriorSlope
public import FLT.Mazur.WeierstrassProductOverlap

/-!
# The original infinity transition on the entire punctured incidence line

The original divided coefficients enter through the actual contraction map.
Only its proved residue identities specialize them. Normalizing by the original
y coordinate sends X/Y to the inverse slope on the whole two-root complement.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ depth) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6)
local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "c" => residue R b6
local notation "P" => SlopeOpen a
local notation "z" => slopeZ a
local notation "A" => algebraMap K P a
local notation "F" => FiberCoordinate a c
open WeierstrassIntegralChart

/-- Restrict the actual original affine contraction to the full punctured incidence line. -/
def residueSlopeOriginalMap : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] P :=
  ((IsScalarTower.toAlgHom R (Polynomial K) P).comp
    ((fiberIncidenceMap a c).restrictScalars R)).comp
      (residueOriginalCoordinateMap D k hk0 hk b3 b4 b6 h3 h4 h6)

/-- The original affine x restricts to the product of the two ordered tangent factors. -/
theorem residueSlopeOriginalMap_x :
    residueSlopeOriginalMap D k hk0 hk b3 b4 b6 h3 h4 h6 (coord W 2 0) = z * (z + A) := by
  change algebraMap (Polynomial K) P (fiberIncidenceMap a c
    (residueOriginalCoordinateMap D k hk0 hk b3 b4 b6 h3 h4 h6 (coord W 2 0))) = _
  rw [residueOriginalCoordinateMap_x, residueNormalMap_x, residueNormalMap_v,
    residueNormalMap_t, IsScalarTower.algebraMap_apply R K F,
    IsScalarTower.algebraMap_apply R K F]
  change algebraMap (Polynomial K) P (fiberIncidenceMap a c (fiberConicFactor a c)) = _
  rw [fiberIncidenceMap_factor]
  exact slopePolynomial_map a

/-- The original affine y is the original x times the slope, with no coefficient discarded. -/
theorem residueSlopeOriginalMap_y :
    residueSlopeOriginalMap D k hk0 hk b3 b4 b6 h3 h4 h6 (coord W 2 1) =
      (z * (z + A)) * z := by
  change algebraMap (Polynomial K) P (fiberIncidenceMap a c
    (residueOriginalCoordinateMap D k hk0 hk b3 b4 b6 h3 h4 h6 (coord W 2 1))) = _
  rw [residueOriginalCoordinateMap_y, residueNormalMap_y, map_mul, map_mul,
    residueNormalMap_v, fiberIncidenceMap_v]
  have hx := residueSlopeOriginalMap_x D k hk0 hk b3 b4 b6 h3 h4 h6
  change algebraMap (Polynomial K) P (fiberIncidenceMap a c
    (residueOriginalCoordinateMap D k hk0 hk b3 b4 b6 h3 h4 h6 (coord W 2 0))) = _ at hx
  rw [residueOriginalCoordinateMap_x] at hx
  exact congrArg (fun t => t * z) hx

/-- The original y is invertible throughout the full slope open. -/
theorem residueSlopeOriginalMap_y_isUnit :
    IsUnit (residueSlopeOriginalMap D k hk0 hk b3 b4 b6 h3 h4 h6 (coord W 2 1)) := by
  rw [residueSlopeOriginalMap_y]
  exact ((slope_units a).1.mul (slope_units a).2.1).mul (slope_units a).1

/-- The original affine-to-infinity overlap retains the actual divided-coordinate map. -/
def residueSlopeOverlap : Overlap W 2 1 →ₐ[R] P :=
  overlapLift W 2 1 (residueSlopeOriginalMap D k hk0 hk b3 b4 b6 h3 h4 h6)
    (residueSlopeOriginalMap_y_isUnit D k hk0 hk b3 b4 b6 h3 h4 h6)

/-- Restriction along the overlap recovers every original affine function. -/
theorem residueSlopeOverlap_base (w : WeierstrassIntegralChart.Coordinate W 2) :
    residueSlopeOverlap D k hk0 hk b3 b4 b6 h3 h4 h6
      (algebraMap _ (Overlap W 2 1) w) =
        residueSlopeOriginalMap D k hk0 hk b3 b4 b6 h3 h4 h6 w :=
  IsLocalization.Away.lift_eq _
    (residueSlopeOriginalMap_y_isUnit D k hk0 hk b3 b4 b6 h3 h4 h6) w

/-- Normalize the original projective coordinates by the actual original y function. -/
def residueSlopeInfinityMap : WeierstrassIntegralChart.Coordinate W 1 →ₐ[R] P :=
  (residueSlopeOverlap D k hk0 hk b3 b4 b6 h3 h4 h6).comp (transitionBase W 2 1)

/-- The infinity X/Y coordinate times the original slope is one on the entire overlap. -/
theorem residueSlopeInfinityMap_x_mul :
    residueSlopeInfinityMap D k hk0 hk b3 b4 b6 h3 h4 h6 (coord W 1 0) * z = 1 := by
  have h := congrArg (residueSlopeOverlap D k hk0 hk b3 b4 b6 h3 h4 h6)
    (overlapInverse_mul W 2 1)
  rw [map_mul, map_one, overlapCoord, residueSlopeOverlap_base,
    residueSlopeOriginalMap_y] at h
  change residueSlopeOverlap D k hk0 hk b3 b4 b6 h3 h4 h6
    (transitionBase W 2 1 (coord W 1 0)) * z = 1
  rw [transitionBase_coord, map_mul, overlapCoord, residueSlopeOverlap_base,
    residueSlopeOriginalMap_x, mul_assoc]
  exact h

/-- The complete infinity transition has X/Y equal to the inverse original slope. -/
theorem residueSlopeInfinityMap_x :
    residueSlopeInfinityMap D k hk0 hk b3 b4 b6 h3 h4 h6 (coord W 1 0) =
      ↑(slope_units a).1.unit⁻¹ := by
  apply (slope_units a).1.mul_right_cancel
  rw [residueSlopeInfinityMap_x_mul]
  exact (Units.inv_mul_eq_one.mpr (slope_units a).1.unit_spec).symm

end FLT.Mazur.WeierstrassModificationX
