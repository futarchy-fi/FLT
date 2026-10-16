/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberTangentFraction

/-!
# Fractional maps on full smoothing nodes

For s = a²t the coordinates p/a+t and q/(q+a) have product t.
The translation by t is essential away from the zero fiber. The reverse
coordinates a(p-t) and -aq/(q-1) retain every function on the tangent opens.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.NodalFiber
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (s t : R) (a : Rˣ) (hs : s = (a : R) ^ 2 * t)
local notation "N" => Coordinate s
local notation "N'" => Coordinate t
local notation "L" => TangentOpen s (a : R)
local notation "M" => TangentOpen t (-1 : R)
local notation "A" => algebraMap R L (a : R)
local notation "Ai" => algebraMap R L (Units.val (a⁻¹))
local notation "T" => algebraMap R L t

include hs in
/-- The translated fractional coordinates satisfy the full nonzero smoothing relation. -/
theorem tangentMobiusForward_relation :
    (Ai * tangentP s (a : R) + T) * tangentFraction s (a : R) = T := by
  apply (tangent_denominator_isUnit s (a : R)).mul_right_cancel
  rw [mul_assoc, tangentFraction_denominator]
  have hi : Ai * A = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have hp := tangent_relation s (a : R)
  have hc : algebraMap R L s = A ^ 2 * T := by
    rw [hs, map_mul, map_pow]
  rw [hc] at hp
  linear_combination Ai * hp + A * T * hi

/-- The entire source node has the translated fractional coordinates, including its node. -/
def tangentMobiusForwardBase : N' →ₐ[R] L :=
  evaluation t (Ai * tangentP s (a : R) + T) (tangentFraction s (a : R))
    (tangentMobiusForward_relation s t a hs)

/-- The fractional coordinates lie in the full target open D(q-1). -/
def tangentMobiusForward : M →ₐ[R] L :=
  IsLocalization.Away.liftAlgHom (q t + algebraMap R N' (-1 : R))
    (f := tangentMobiusForwardBase s t a hs) (by
      simp only [tangentMobiusForwardBase, map_neg, map_one, ← sub_eq_add_neg,
        map_sub, evaluation_q]
      exact tangentFraction_sub_one_isUnit s (a : R) a.isUnit)

/-- Localization preserves every target node function. -/
theorem tangentMobiusForward_base (z : N') :
    tangentMobiusForward s t a hs (algebraMap N' M z) =
      tangentMobiusForwardBase s t a hs z := by
  rw [tangentMobiusForward, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

@[simp] theorem tangentMobiusForward_p :
    tangentMobiusForward s t a hs (tangentP t (-1 : R)) =
      Ai * tangentP s (a : R) + T := by
  rw [tangentP, tangentMobiusForward_base]
  exact evaluation_p ..

@[simp] theorem tangentMobiusForward_q :
    tangentMobiusForward s t a hs (tangentQ t (-1 : R)) =
      tangentFraction s (a : R) := by
  rw [tangentQ, tangentMobiusForward_base]
  exact evaluation_q ..

include hs in
/-- The reverse translated coordinates recover the original smoothing parameter. -/
theorem tangentMobiusBackward_relation :
    (algebraMap R M (a : R) * (tangentP t (-1 : R) - algebraMap R M t)) *
      (-algebraMap R M (a : R) * tangentFraction t (-1 : R)) = algebraMap R M s := by
  apply (tangent_denominator_isUnit t (-1 : R)).mul_right_cancel
  have hf := tangentFraction_denominator t (-1 : R)
  have hp := tangent_relation t (-1 : R)
  rw [hs, map_mul, map_pow]
  simp only [map_neg, map_one] at hf ⊢
  linear_combination
    -(algebraMap R M (a : R)) ^ 2 *
      (tangentP t (-1 : R) - algebraMap R M t) * hf -
    (algebraMap R M (a : R)) ^ 2 * hp

/-- Reverse coordinates on every function of the original node. -/
def tangentMobiusBackwardBase : N →ₐ[R] M :=
  evaluation s (algebraMap R M (a : R) * (tangentP t (-1 : R) - algebraMap R M t))
    (-algebraMap R M (a : R) * tangentFraction t (-1 : R))
    (tangentMobiusBackward_relation s t a hs)

/-- The reverse fractional coordinates land in the original tangent open. -/
def tangentMobiusBackward : L →ₐ[R] M :=
  IsLocalization.Away.liftAlgHom (q s + algebraMap R N (a : R))
    (f := tangentMobiusBackwardBase s t a hs) (by
      simp only [map_add, tangentMobiusBackwardBase, evaluation_q, AlgHom.commutes]
      have he : -algebraMap R M (a : R) * tangentFraction t (-1 : R) +
          algebraMap R M (a : R) =
          -algebraMap R M (a : R) * (tangentFraction t (-1 : R) - 1) := by ring
      rw [he]
      exact (a.isUnit.map (algebraMap R M)).neg.mul
        (tangentFraction_sub_one_isUnit t (-1 : R) (isUnit_one.neg)))

/-- Reverse localization retains every original node function. -/
theorem tangentMobiusBackward_base (z : N) :
    tangentMobiusBackward s t a hs (algebraMap N L z) =
      tangentMobiusBackwardBase s t a hs z := by
  rw [tangentMobiusBackward, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

@[simp] theorem tangentMobiusBackward_p :
    tangentMobiusBackward s t a hs (tangentP s (a : R)) =
      algebraMap R M (a : R) * (tangentP t (-1 : R) - algebraMap R M t) := by
  rw [tangentP, tangentMobiusBackward_base]
  exact evaluation_p ..

@[simp] theorem tangentMobiusBackward_q :
    tangentMobiusBackward s t a hs (tangentQ s (a : R)) =
      -algebraMap R M (a : R) * tangentFraction t (-1 : R) := by
  rw [tangentQ, tangentMobiusBackward_base]
  exact evaluation_q ..

end FLT.Mazur.NodalFiber
