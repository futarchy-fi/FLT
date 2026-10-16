/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberZeroTangentFraction

/-!
# Full zero-node fractional coordinate maps in both directions

The forward coordinates are p/a and q/(q+a). The reverse coordinates are
ap and -aq/(q-1). Each map is defined on its entire tangent neighborhood.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.NodalFiber
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (a : Rˣ)
local notation "N" => Coordinate (0 : R)
local notation "L" => ZeroTangentOpen (a : R)
local notation "M" => ZeroTangentOpen (-1 : R)
local notation "A" => algebraMap R M (a : R)

/-- The normalized first coordinate and fractional second coordinate on the source open. -/
def zeroTangentMobiusForwardBase : N →ₐ[R] L :=
  evaluation 0 (algebraMap R L (↑a⁻¹ : R) * zeroTangentP (a : R))
    (zeroTangentFraction (a : R)) (by
      rw [mul_assoc, zeroTangentFraction_relation, mul_zero, map_zero])

/-- The forward coordinates land in the whole target open D(q-1). -/
def zeroTangentMobiusForward : M →ₐ[R] L :=
  IsLocalization.Away.liftAlgHom (q (0 : R) + algebraMap R N (-1 : R))
    (f := zeroTangentMobiusForwardBase a) (by
      simp only [zeroTangentMobiusForwardBase, map_neg, map_one, ← sub_eq_add_neg,
        map_sub, evaluation_q]
      exact zeroTangentFraction_sub_one_isUnit (a : R) a.isUnit)

/-- Forward localization retains the entire universal node map. -/
theorem zeroTangentMobiusForward_base (z : N) :
    zeroTangentMobiusForward a (algebraMap N M z) = zeroTangentMobiusForwardBase a z := by
  rw [zeroTangentMobiusForward, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

@[simp] theorem zeroTangentMobiusForward_p :
    zeroTangentMobiusForward a (zeroTangentP (-1 : R)) =
      algebraMap R L (↑a⁻¹ : R) * zeroTangentP (a : R) := by
  rw [zeroTangentP, zeroTangentMobiusForward_base]
  exact evaluation_p ..

@[simp] theorem zeroTangentMobiusForward_q :
    zeroTangentMobiusForward a (zeroTangentQ (-1 : R)) =
      zeroTangentFraction (a : R) := by
  rw [zeroTangentQ, zeroTangentMobiusForward_base]
  exact evaluation_q ..

/-- The reverse full-node coordinates recover the original tangent scale. -/
def zeroTangentMobiusBackwardBase : N →ₐ[R] M :=
  evaluation 0 (A * zeroTangentP (-1 : R)) (-A * zeroTangentFraction (-1 : R)) (by
    rw [map_zero]
    calc _ = -(A * A) * (zeroTangentP (-1 : R) * zeroTangentFraction (-1 : R)) := by ring
      _ = 0 := by rw [zeroTangentFraction_relation, mul_zero])

/-- The reverse coordinates land in the whole original open D(q+a). -/
def zeroTangentMobiusBackward : L →ₐ[R] M :=
  IsLocalization.Away.liftAlgHom (q (0 : R) + algebraMap R N (a : R))
    (f := zeroTangentMobiusBackwardBase a) (by
      simp only [map_add, zeroTangentMobiusBackwardBase, evaluation_q, AlgHom.commutes]
      have he : -A * zeroTangentFraction (-1 : R) + A =
          -A * (zeroTangentFraction (-1 : R) - 1) := by ring
      rw [he]
      exact (a.isUnit.map (algebraMap R M)).neg.mul
        (zeroTangentFraction_sub_one_isUnit (-1 : R) (isUnit_one.neg)))

/-- Reverse localization retains every universal node function. -/
theorem zeroTangentMobiusBackward_base (z : N) :
    zeroTangentMobiusBackward a (algebraMap N L z) = zeroTangentMobiusBackwardBase a z := by
  rw [zeroTangentMobiusBackward, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

@[simp] theorem zeroTangentMobiusBackward_p :
    zeroTangentMobiusBackward a (zeroTangentP (a : R)) =
      A * zeroTangentP (-1 : R) := by
  rw [zeroTangentP, zeroTangentMobiusBackward_base]
  exact evaluation_p ..

@[simp] theorem zeroTangentMobiusBackward_q :
    zeroTangentMobiusBackward a (zeroTangentQ (a : R)) =
      -A * zeroTangentFraction (-1 : R) := by
  rw [zeroTangentQ, zeroTangentMobiusBackward_base]
  exact evaluation_q ..

end FLT.Mazur.NodalFiber
