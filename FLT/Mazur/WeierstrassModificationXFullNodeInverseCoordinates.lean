/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeOpen

/-!
# Inverse coordinates on the full node open

For d=1-c*p², put t=a*p/d and v=q+a*c*p²/d. These satisfy the original
full fiber equation. In particular the conic factor becomes q*(v+a),
so both original components remain visible in the actual substitution.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (a c : R)
local notation "L" => FullNodeOpen a c
local notation "P" => fullNodeP a c
local notation "Q" => fullNodeQ a c
local notation "A" => algebraMap R L a
local notation "C" => algebraMap R L c
local notation "D" => (1 - C * P ^ 2)

/-- The inverse of the parameter denominator, as a unit of the actual node open. -/
def fullNodeInv : L := ↑((fullNode_parameter_isUnit a c).unit⁻¹)
local notation "I" => fullNodeInv a c

/-- The chosen inverse cancels the parameter denominator. -/
theorem fullNode_mul_inv : D * I = 1 := by
  exact (fullNode_parameter_isUnit a c).mul_val_inv

/-- The inverse parameter denominator is a unit. -/
theorem fullNodeInv_isUnit : IsUnit I := Units.isUnit _

/-- The parameter denominator acts identically on the second node branch. -/
theorem fullNode_denominator_q : D * Q = Q := by
  calc D * Q = Q - C * P * (P * Q) := by ring
    _ = Q := by rw [fullNode_relation, mul_zero, sub_zero]

/-- The inverse denominator also fixes the second node coordinate. -/
theorem fullNode_inv_q : I * Q = Q := by
  apply (fullNode_parameter_isUnit a c).mul_left_cancel
  rw [← mul_assoc, fullNode_mul_inv, one_mul, fullNode_denominator_q]

/-- The inverse incidence coordinate on the node open. -/
def fullNodeInverseT : L := A * P * I
/-- The inverse slope coordinate on the node open. -/
def fullNodeInverseV : L := Q + A * C * P ^ 2 * I
local notation "T" => fullNodeInverseT a c
local notation "V" => fullNodeInverseV a c

/-- The original opposite tangent factor is the quotient (q+a)/d. -/
theorem fullNodeInverseV_add : V + A = (Q + A) * I := by
  have h := fullNode_mul_inv a c
  dsimp [fullNodeInverseV]
  calc Q + A * C * P ^ 2 * I + A =
      Q + A * C * P ^ 2 * I + A * (D * I) := by rw [h, mul_one]
    _ = Q + A * I := by ring
    _ = (Q + A) * I := by rw [add_mul, mul_comm Q I, fullNode_inv_q]

/-- The inverse coordinates retain the incidence parameter identity. -/
theorem fullNodeInverse_parameter_mul : P * (V + A) = T := by
  rw [fullNodeInverseV_add, ← mul_assoc, mul_add, fullNode_relation, zero_add]
  dsimp [fullNodeInverseT]
  ring

/-- The original conic factor is the second node coordinate times a unit. -/
theorem fullNodeInverse_conic : V * (V + A) - C * T ^ 2 = Q * (V + A) := by
  have hpq := fullNode_relation a c
  rw [fullNodeInverseV_add]
  dsimp [fullNodeInverseV, fullNodeInverseT]
  calc (Q + A * C * P ^ 2 * I) * ((Q + A) * I) - C * (A * P * I) ^ 2 =
      Q * ((Q + A) * I) + A * C * P * I ^ 2 * (P * Q) := by ring
    _ = Q * ((Q + A) * I) := by rw [hpq, mul_zero, add_zero]

/-- Both original components satisfy the full fiber equation after substitution. -/
theorem fullNodeInverse_relation : T * (V * (V + A) - C * T ^ 2) = 0 := by
  rw [fullNodeInverse_conic]
  dsimp [fullNodeInverseT]
  calc A * P * I * (Q * (V + A)) = A * I * (V + A) * (P * Q) := by ring
    _ = 0 := by rw [fullNode_relation, mul_zero]

/-- The opposite tangent factor of the inverse substitution is invertible. -/
theorem fullNodeInverseV_add_isUnit : IsUnit (V + A) := by
  rw [fullNodeInverseV_add]
  exact (fullNode_tangent_isUnit a c).mul (fullNodeInv_isUnit a c)

/-- The inverse coordinate substitution is an actual map out of the full fiber. -/
def fullFiberToNodeBase : FiberCoordinate a c →ₐ[R] L :=
  fiberEvaluation a c T V (fullNodeInverse_relation a c)

/-- Substitution retains the original incidence coordinate. -/
@[simp] theorem fullFiberToNodeBase_t : fullFiberToNodeBase a c (fiberT a c) = T :=
  fiberEvaluation_t _ _ _ _ _
/-- Substitution retains the original slope coordinate. -/
@[simp] theorem fullFiberToNodeBase_v : fullFiberToNodeBase a c (fiberV a c) = V :=
  fiberEvaluation_v _ _ _ _ _

/-- The inverse substitution extends to the actual tangent localization. -/
def fullFiberToNode : FullFirstFiberOpen a c →ₐ[R] L :=
  IsLocalization.Away.liftAlgHom (f := fullFiberToNodeBase a c)
    (fiberV a c + algebraMap R _ a) (by
      simpa only [map_add, fullFiberToNodeBase_v, AlgHom.commutes] using
        fullNodeInverseV_add_isUnit a c)

/-- The localized inverse uses the original coordinate substitution. -/
theorem fullFiberToNode_base (x : FiberCoordinate a c) :
    fullFiberToNode a c (algebraMap (FiberCoordinate a c) _ x) =
      fullFiberToNodeBase a c x := by
  rw [fullFiberToNode, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

end FLT.Mazur.WeierstrassModificationX
