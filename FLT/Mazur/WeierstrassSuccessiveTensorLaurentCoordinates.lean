/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveTensorLaurentEvaluation
public import FLT.Mazur.WeierstrassSuccessiveLaurentBoundary
public import FLT.Mazur.WeierstrassSuccessiveXLocalization

/-!
# Original integral functions in the arithmetic tensor Laurent evaluations

Both boundary coordinates, the inverse incidence unit, and the original
slope retain their exact Laurent values after coefficient extension.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S]
  (r : SuccessiveIncidence.Coordinate (algebraMap R S π))
  (hr : r ^ 2 + nodeSlopeLinear (W.map (algebraMap R S))
    (algebraMap R S π) (algebraMap R S b3) * r =
    nodeSlopeConstant (W.map (algebraMap R S)) (algebraMap R S s)
      (algebraMap R S π) (algebraMap R S b4) (algebraMap R S b6))
local notation "q" => algebraMap R S
local notation "t" => coord W s π b3 b4 b6 0
local notation "u" => coord W s π b3 b4 b6 2
local notation "v" => coord W s π b3 b4 b6 1
local notation "L" => tensorInverseLeftSlopeLaurent W s π b3 b4 b6 S r hr
local notation "U" => tensorRightSlopeLaurent W s π b3 b4 b6 S r hr

/-- The original old incidence unit is the inverse next edge coordinate. -/
theorem tensorInverseLeftSlopeLaurent_coordinate :
    L (PrincipalOpenTensor.coefficient S t (algebraMap _ _ t)) =
      LaurentPolynomial.T (-1) := by
  rw [PrincipalOpenTensor.coefficient_base]
  change L (algebraMap _ _ (tensorCoord W s π b3 b4 b6 S 0)) = _
  rw [tensorInverseLeftSlopeLaurent_base, tensorSlopePolygonRetraction_left,
    PolygonSmoothing.leftLaurentMap_left]
  exact LaurentPolynomial.invert_T 1

/-- The original localized inverse incidence unit is the next edge coordinate. -/
theorem tensorInverseLeftSlopeLaurent_inverse :
    L (PrincipalOpenTensor.coefficient S t (↑(xOpenUnit W s π b3 b4 b6)⁻¹)) =
      LaurentPolynomial.T 1 := by
  apply map_inverse_unit
    ((L).toRingHom.comp (PrincipalOpenTensor.coefficient S t).toRingHom)
    (xOpenUnit W s π b3 b4 b6) (LaurentUnitPoints.pointUnit (AlgHom.id S S[T;T⁻¹]))
  change L (PrincipalOpenTensor.coefficient S t (↑(xOpenUnit W s π b3 b4 b6))) = _
  rw [xOpenUnit_val, tensorInverseLeftSlopeLaurent_coordinate]
  rfl

/-- The old original tensor slope is evaluated in exactly the inverted edge coordinate. -/
theorem tensorInverseLeftSlopeLaurent_slope :
    L (PrincipalOpenTensor.coefficient S t (algebraMap _ _ v)) =
      inverseLeftIncidenceLaurent (q π) r := by
  rw [PrincipalOpenTensor.coefficient_base]
  change L (algebraMap _ _ (tensorCoord W s π b3 b4 b6 S 1)) = _
  rw [tensorInverseLeftSlopeLaurent_base, tensorSlopePolygonRetraction_slope]
  rfl

/-- The next original horizontal coordinate is the unchanged Laurent variable. -/
theorem tensorRightSlopeLaurent_coordinate :
    U (PrincipalOpenTensor.coefficient S u (algebraMap _ _ u)) = LaurentPolynomial.T 1 := by
  rw [PrincipalOpenTensor.coefficient_base]
  change U (algebraMap _ _ (tensorCoord W s π b3 b4 b6 S 2)) = _
  rw [tensorRightSlopeLaurent_base, tensorSlopePolygonRetraction_right,
    PolygonSmoothing.branchSwapMap_right, PolygonSmoothing.leftLaurentMap_left]

/-- The next original tensor slope keeps its full right Laurent evaluation. -/
theorem tensorRightSlopeLaurent_slope :
    U (PrincipalOpenTensor.coefficient S u (algebraMap _ _ v)) =
      rightIncidenceLaurent (q π) r := by
  rw [PrincipalOpenTensor.coefficient_base]
  change U (algebraMap _ _ (tensorCoord W s π b3 b4 b6 S 1)) = _
  rw [tensorRightSlopeLaurent_base, tensorSlopePolygonRetraction_slope]
  rfl

end FLT.Mazur.WeierstrassSuccessiveX
