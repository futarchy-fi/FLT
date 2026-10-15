/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveTensorLaurentCoordinates
public import FLT.Mazur.WeierstrassDividedPreviousBoundaryAlgebra
public import FLT.Mazur.WeierstrassModificationXLocalization

/-!
# Original initial divided functions on a constructed Laurent branch

The actual preceding transition retains x = z and y = z times the full
constructed slope. No reduction to the residue field is used.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k : ℕ}
  (d : Data W π k) (e : Data W π (k + 1))
  (S : Type u) [CommRing S] [Algebra R S]
  (r : SuccessiveIncidence.Coordinate (algebraMap R S π))
  (hr : r ^ 2 + nodeSlopeLinear (W.map (algebraMap R S))
    (algebraMap R S π) (algebraMap R S e.b3) * r =
    nodeSlopeConstant (W.map (algebraMap R S)) (algebraMap R S (π ^ k))
      (algebraMap R S π) (algebraMap R S e.b4) (algebraMap R S e.b6))
local notation "x" => WeierstrassDilatation.x W (π ^ k) d.b3 d.b4 d.b6
local notation "y" => WeierstrassDilatation.y W (π ^ k) d.b3 d.b4 d.b6
local notation "u₁" => coord W (π ^ k) π e.b3 e.b4 e.b6 2
local notation "B" => PrincipalOpenTensor.transition S x u₁ (previousBoundaryEquiv hπ d e)
local notation "U" => tensorRightSlopeLaurent W (π ^ k) π e.b3 e.b4 e.b6 S r hr

/-- The original initial divided localization evaluated through its actual next branch. -/
def initialDividedSlopeLaurent := (U).comp (B).toAlgHom

/-- The initial divided unit keeps the next branch's original Laurent coordinate. -/
theorem initialDividedSlopeLaurent_x :
    initialDividedSlopeLaurent hπ d e S r hr
      (PrincipalOpenTensor.coefficient S x (algebraMap _ _ x)) = LaurentPolynomial.T 1 := by
  change U (B _) = _
  rw [PrincipalOpenTensor.transition_coefficient, previousBoundaryEquiv_base,
    WeierstrassDilatation.parameterEquiv_x, fromDivided_x, tensorRightSlopeLaurent_coordinate]

/-- Its inverse retains the reciprocal Laurent coordinate. -/
theorem initialDividedSlopeLaurent_inverse :
    initialDividedSlopeLaurent hπ d e S r hr
      (PrincipalOpenTensor.coefficient S x
        (↑(WeierstrassModificationX.dividedOpenUnit W (π ^ k) d.b3 d.b4 d.b6)⁻¹)) =
      LaurentPolynomial.T (-1) := by
  apply WeierstrassModificationX.map_inverse_unit
    ((initialDividedSlopeLaurent hπ d e S r hr).toRingHom.comp
      (PrincipalOpenTensor.coefficient S x).toRingHom)
    (WeierstrassModificationX.dividedOpenUnit W (π ^ k) d.b3 d.b4 d.b6)
    (LaurentUnitPoints.pointUnit (AlgHom.id S S[T;T⁻¹]))⁻¹
  change initialDividedSlopeLaurent hπ d e S r hr
    (PrincipalOpenTensor.coefficient S x
      (↑(WeierstrassModificationX.dividedOpenUnit W (π ^ k) d.b3 d.b4 d.b6))) = _
  rw [WeierstrassModificationX.dividedOpenUnit_val, initialDividedSlopeLaurent_x]
  rfl

/-- The original vertical function is the Laurent coordinate times the complete slope. -/
theorem initialDividedSlopeLaurent_y :
    initialDividedSlopeLaurent hπ d e S r hr
      (PrincipalOpenTensor.coefficient S x (algebraMap _ _ y)) =
      LaurentPolynomial.T 1 * rightIncidenceLaurent (algebraMap R S π) r := by
  change U (B _) = _
  rw [PrincipalOpenTensor.transition_coefficient, previousBoundaryEquiv_base,
    WeierstrassDilatation.parameterEquiv_y, fromDivided_y, map_mul, map_mul, map_mul,
    tensorRightSlopeLaurent_coordinate, tensorRightSlopeLaurent_slope]

end FLT.Mazur.WeierstrassDividedDepth
