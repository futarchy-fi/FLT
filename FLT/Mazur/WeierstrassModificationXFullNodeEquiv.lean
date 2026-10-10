/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeInverseCoordinates

/-!
# The full ambient node equivalence

Both compositions are proved on the original coordinates by cancellation of
units. The resulting equivalence keeps the conic coefficient and includes
both components at their incidence intersection.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (a c : R) (ha : IsUnit a)
local notation "F" => FiberCoordinate a c
local notation "O" => FullFirstFiberOpen a c
local notation "L" => FullNodeOpen a c
local notation "f" => fullNodeToFiber a c ha
local notation "g" => fullFiberToNode a c
local notation "z" => fullFirstFiberParameter a c
local notation "w" => fullFirstFiberNodeSlope a c
local notation "U" => algebraMap F O (fiberV a c + algebraMap R F a)
local notation "T" => algebraMap F O (fiberT a c)
local notation "V" => algebraMap F O (fiberV a c)
local notation "A" => algebraMap R O a
local notation "C" => algebraMap R O c

/-- The mapped inverse denominator recovers the full opposite tangent factor. -/
theorem fullNodeToFiber_inv_mul : f (fullNodeInv a c) * A = U - w := by
  have h := congrArg f (fullNode_mul_inv a c)
  simp only [map_mul, map_sub, map_one, map_pow, AlgHom.commutes,
    fullNodeToFiber_p] at h
  apply (fullFirstFiber_denominator_isUnit a c ha).mul_left_cancel
  calc (1 - C * z ^ 2) * (f (fullNodeInv a c) * A) = A := by
        rw [← mul_assoc, h, one_mul]
    _ = (1 - C * z ^ 2) * (U - w) := by
      rw [mul_sub, fullFirstFiber_denominator_mul, fullFirstFiber_denominator_slope]
      ring

/-- The inverse incidence expression returns the original coordinate. -/
theorem fullNodeToFiber_inverseT : f (fullNodeInverseT a c) = T := by
  rw [fullNodeInverseT, map_mul, map_mul, AlgHom.commutes, fullNodeToFiber_p]
  calc A * z * f (fullNodeInv a c) = z * (f (fullNodeInv a c) * A) := by ring
    _ = z * (U - w) := by rw [fullNodeToFiber_inv_mul]
    _ = T := by
      rw [mul_sub, fullFirstFiberParameter_mul, fullFirstFiber_node_relation, sub_zero]

/-- The inverse slope expression returns the original coordinate. -/
theorem fullNodeToFiber_inverseV : f (fullNodeInverseV a c) = V := by
  rw [fullNodeInverseV, map_add, map_mul, map_mul, map_mul, map_pow,
    AlgHom.commutes, AlgHom.commutes, fullNodeToFiber_p, fullNodeToFiber_q]
  calc w + A * C * z ^ 2 * f (fullNodeInv a c) =
      w + C * z ^ 2 * (f (fullNodeInv a c) * A) := by ring
    _ = w + C * z ^ 2 * U - C * z * (z * w) := by
      rw [fullNodeToFiber_inv_mul]
      ring
    _ = V := by
      rw [fullFirstFiber_node_relation, mul_zero, sub_zero]
      dsimp [fullFirstFiberNodeSlope]
      ring

/-- The reverse map sends the original rational incidence parameter to p. -/
theorem fullFiberToNode_parameter : g z = fullNodeP a c := by
  have h := congrArg g (fullFirstFiberParameter_mul a c)
  rw [map_mul, fullFiberToNode_base, fullFiberToNode_base, fullFiberToNodeBase_t,
    map_add, fullFiberToNodeBase_v, AlgHom.commutes] at h
  apply (fullNodeInverseV_add_isUnit a c).mul_right_cancel
  exact h.trans (fullNodeInverse_parameter_mul a c).symm

/-- The reverse map sends the corrected conic slope to q. -/
theorem fullFiberToNode_slope : g w = fullNodeQ a c := by
  have h := congrArg g (fullFirstFiber_denominator_mul a c)
  simp only [map_mul, map_sub, map_one, map_pow, map_add, AlgHom.commutes,
    fullFiberToNode_parameter, fullFiberToNode_base, fullFiberToNodeBase_v] at h
  have hd : (1 - algebraMap R L c * fullNodeP a c ^ 2) *
      (fullNodeInverseV a c + algebraMap R L a) =
      fullNodeQ a c + algebraMap R L a := by
    rw [fullNodeInverseV_add]
    calc _ = (fullNodeQ a c + algebraMap R L a) *
        ((1 - algebraMap R L c * fullNodeP a c ^ 2) * fullNodeInv a c) := by ring
      _ = _ := by rw [fullNode_mul_inv, mul_one]
  exact add_right_cancel (h.symm.trans hd)

/-- The composite on the original full tangent neighborhood is the identity. -/
theorem fullNodeToFiber_comp : (f).comp g = AlgHom.id R O := by
  apply IsLocalization.algHom_ext (Submonoid.powers (fiberV a c + algebraMap R F a))
  apply fiber_hom_ext a c
  · change f (g T) = T
    rw [fullFiberToNode_base, fullFiberToNodeBase_t, fullNodeToFiber_inverseT]
  · change f (g V) = V
    rw [fullFiberToNode_base, fullFiberToNodeBase_v, fullNodeToFiber_inverseV]

/-- The composite on the actual product-zero node open is the identity. -/
theorem fullFiberToNode_comp : (g).comp f = AlgHom.id R L := by
  apply IsLocalization.algHom_ext (Submonoid.powers (fullNodeDenominator a c))
  apply NodalFiber.hom_ext 0
  · change g (f (fullNodeP a c)) = fullNodeP a c
    rw [fullNodeToFiber_p, fullFiberToNode_parameter]
  · change g (f (fullNodeQ a c)) = fullNodeQ a c
    rw [fullNodeToFiber_q, fullFiberToNode_slope]

/-- The actual full fiber neighborhood is isomorphic to an open of pq=0. -/
def fullFirstNodeEquiv : O ≃ₐ[R] L :=
  AlgEquiv.ofAlgHom g f (fullFiberToNode_comp a c ha) (fullNodeToFiber_comp a c ha)

/-- The equivalence uses the proved inverse-coordinate map. -/
theorem fullFirstNodeEquiv_toAlgHom :
    (fullFirstNodeEquiv a c ha).toAlgHom = g := rfl
/-- Its inverse uses the original rational coordinates on the full fiber. -/
theorem fullFirstNodeEquiv_symm_toAlgHom :
    (fullFirstNodeEquiv a c ha).symm.toAlgHom = f := rfl

end FLT.Mazur.WeierstrassModificationX
