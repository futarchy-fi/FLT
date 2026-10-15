/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialSlopeLaurent
public import FLT.Mazur.WeierstrassModificationXTensorOverlapCoordinates

/-!
# Original initial tensor coordinates on the full arithmetic Laurent boundary

Both integral transitions are retained. The initial incidence is the inverse
edge coordinate, while its slope is the complete next-branch slope.
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
local notation "t₀" => WeierstrassModificationX.t W (π ^ k) d.b3 d.b4 d.b6
local notation "v₀" => WeierstrassModificationX.v W (π ^ k) d.b3 d.b4 d.b6
local notation "A" => PrincipalOpenTensor.transition S x t₀
  (WeierstrassModificationX.overlapEquiv W (π ^ k) d.b3 d.b4 d.b6)
local notation "L" => initialDividedSlopeLaurent hπ d e S r hr

/-- Evaluate the original initial tensor localization through both actual transitions. -/
@[irreducible] def initialTensorSlopeLaurent := (L).comp (A).symm.toAlgHom

/-- The original initial incidence coordinate is exactly the inverse Laurent parameter. -/
theorem initialTensorSlopeLaurent_t :
    initialTensorSlopeLaurent hπ d e S r hr
      (PrincipalOpenTensor.coefficient S t₀ (algebraMap _ _ t₀)) =
      LaurentPolynomial.T (-1) := by
  rw [initialTensorSlopeLaurent]
  change L ((A).symm _) = _
  rw [PrincipalOpenTensor.transition_symm_coefficient]
  change L (PrincipalOpenTensor.coefficient S x
    (WeierstrassModificationX.overlapBackward W (π ^ k) d.b3 d.b4 d.b6 _)) = _
  rw [WeierstrassModificationX.overlapBackward_base,
    WeierstrassModificationX.xToDividedOpen, WeierstrassModificationX.xOverlapMap_t,
    initialDividedSlopeLaurent_inverse]

/-- The full original slope is preserved, including its nilpotent coefficient corrections. -/
theorem initialTensorSlopeLaurent_v :
    initialTensorSlopeLaurent hπ d e S r hr
      (PrincipalOpenTensor.coefficient S t₀ (algebraMap _ _ v₀)) =
      rightIncidenceLaurent (algebraMap R S π) r := by
  rw [initialTensorSlopeLaurent]
  change L ((A).symm _) = _
  rw [PrincipalOpenTensor.transition_symm_coefficient]
  change L (PrincipalOpenTensor.coefficient S x
    (WeierstrassModificationX.overlapBackward W (π ^ k) d.b3 d.b4 d.b6 _)) = _
  rw [WeierstrassModificationX.overlapBackward_base,
    WeierstrassModificationX.xToDividedOpen, WeierstrassModificationX.xOverlapMap_v,
    map_mul, map_mul, initialDividedSlopeLaurent_inverse]
  change LaurentPolynomial.T (-1) * L (PrincipalOpenTensor.coefficient S x
    (algebraMap _ _ (WeierstrassDilatation.y W (π ^ k) d.b3 d.b4 d.b6))) = _
  rw [initialDividedSlopeLaurent_y,
    ← mul_assoc, ← LaurentPolynomial.T_add]
  simp only [neg_add_cancel, LaurentPolynomial.T_zero, one_mul]

/-- The inverse original incidence unit recovers the original edge parameter. -/
theorem initialTensorSlopeLaurent_inverse :
    initialTensorSlopeLaurent hπ d e S r hr
      (PrincipalOpenTensor.coefficient S t₀
        (↑(WeierstrassModificationX.xOpenUnit W (π ^ k) d.b3 d.b4 d.b6)⁻¹)) =
      LaurentPolynomial.T 1 := by
  apply WeierstrassModificationX.map_inverse_unit
    ((initialTensorSlopeLaurent hπ d e S r hr).toRingHom.comp
      (PrincipalOpenTensor.coefficient S t₀).toRingHom)
    (WeierstrassModificationX.xOpenUnit W (π ^ k) d.b3 d.b4 d.b6)
    (LaurentUnitPoints.pointUnit (AlgHom.id S S[T;T⁻¹]))
  change initialTensorSlopeLaurent hπ d e S r hr
    (PrincipalOpenTensor.coefficient S t₀
      (↑(WeierstrassModificationX.xOpenUnit W (π ^ k) d.b3 d.b4 d.b6))) = _
  rw [WeierstrassModificationX.xOpenUnit_val, initialTensorSlopeLaurent_t]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
