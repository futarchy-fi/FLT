/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberTangentMobiusMaps

/-!
# The full smoothing-node fractional coordinate equivalence

The two maps are inverse on every localized node function. In particular,
this coordinate change is a genuine full-neighborhood isomorphism, unlike
retaining the original incidence coordinate on the whole chart.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.NodalFiber
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (s t : R) (a : Rˣ) (hs : s = (a : R) ^ 2 * t)
local notation "N" => Coordinate s
local notation "L" => TangentOpen s (a : R)
local notation "M" => TangentOpen t (-1 : R)
local notation "F" => tangentMobiusForward s t a hs
local notation "G" => tangentMobiusBackward s t a hs
local notation "A" => algebraMap R L (a : R)
local notation "Ai" => algebraMap R L (Units.val (a⁻¹))

/-- The forward map recovers the unnormalized second coordinate from the target fraction. -/
theorem tangentMobiusForward_fraction :
    F (tangentFraction t (-1 : R)) = -Ai * tangentQ s (a : R) := by
  have h := congrArg F (tangentFraction_denominator t (-1 : R))
  simp only [map_mul, map_sub, tangentMobiusForward_q,
    map_neg, map_one, ← sub_eq_add_neg] at h
  apply (tangentFraction_sub_one_isUnit s (a : R) a.isUnit).mul_right_cancel
  rw [h, tangentFraction_sub_one, tangentFraction]
  have hi : Ai * A = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  symm
  calc _ = (Ai * A) * (tangentQ s (a : R) *
        ↑((tangent_denominator_isUnit s (a : R)).unit⁻¹)) := by ring
    _ = _ := by rw [hi, one_mul]

/-- The reverse map sends the source fraction back to the whole target second coordinate. -/
theorem tangentMobiusBackward_fraction :
    G (tangentFraction s (a : R)) = tangentQ t (-1 : R) := by
  have h := congrArg G (tangentFraction_denominator s (a : R))
  simp only [map_mul, map_add, AlgHom.commutes, tangentMobiusBackward_q] at h
  have hu := (tangent_denominator_isUnit s (a : R)).map (G).toRingHom
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_add,
    AlgHom.commutes, tangentMobiusBackward_q] at hu
  apply hu.mul_right_cancel
  rw [h]
  have hd := tangentFraction_denominator t (-1 : R)
  simp only [map_neg, map_one] at hd
  linear_combination algebraMap R M (a : R) * hd

/-- The forward map followed algebraically by the reverse fixes the whole source open. -/
theorem tangentMobiusForward_backward : (F).comp G = AlgHom.id R L := by
  apply IsLocalization.algHom_ext (Submonoid.powers (q s + algebraMap R N (a : R)))
  apply hom_ext
  · change F (G (tangentP s (a : R))) = tangentP s (a : R)
    rw [tangentMobiusBackward_p, map_mul, map_sub, AlgHom.commutes,
      tangentMobiusForward_p, AlgHom.commutes, add_sub_cancel_right,
      ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
  · change F (G (tangentQ s (a : R))) = tangentQ s (a : R)
    rw [tangentMobiusBackward_q, map_mul, map_neg, AlgHom.commutes,
      tangentMobiusForward_fraction]
    calc _ = (A * Ai) * tangentQ s (a : R) := by ring
      _ = _ := by rw [← map_mul, Units.mul_inv, map_one, one_mul]

/-- The reverse composite fixes every function on the target tangent open. -/
theorem tangentMobiusBackward_forward : (G).comp F = AlgHom.id R M := by
  apply IsLocalization.algHom_ext (Submonoid.powers (q t + algebraMap R (Coordinate t) (-1 : R)))
  apply hom_ext
  · change G (F (tangentP t (-1 : R))) = tangentP t (-1 : R)
    rw [tangentMobiusForward_p, map_add, map_mul, AlgHom.commutes, tangentMobiusBackward_p,
      ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul, AlgHom.commutes, sub_add_cancel]
  · change G (F (tangentQ t (-1 : R))) = tangentQ t (-1 : R)
    rw [tangentMobiusForward_q, tangentMobiusBackward_fraction]

/-- The entire D(q+a) node has fractional coordinates on the entire D(q-1) node. -/
def tangentMobiusEquiv : M ≃ₐ[R] L :=
  AlgEquiv.ofAlgHom F G (tangentMobiusForward_backward s t a hs)
    (tangentMobiusBackward_forward s t a hs)

/-- The full equivalence retains the translated first coordinate. -/
@[simp] theorem tangentMobiusEquiv_p :
    tangentMobiusEquiv s t a hs (tangentP t (-1 : R)) =
      Ai * tangentP s (a : R) + algebraMap R L t :=
  tangentMobiusForward_p s t a hs

/-- The full equivalence retains the fractional second coordinate. -/
@[simp] theorem tangentMobiusEquiv_q :
    tangentMobiusEquiv s t a hs (tangentQ t (-1 : R)) = tangentFraction s (a : R) :=
  tangentMobiusForward_q s t a hs

end FLT.Mazur.NodalFiber
