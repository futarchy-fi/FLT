/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberZeroTangentMobiusMaps

/-!
# The full zero-node fractional coordinate equivalence

The two maps are inverse on every localized node function. In particular,
this coordinate change is a genuine full-neighborhood isomorphism, unlike
retaining the original incidence coordinate on the whole chart.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.NodalFiber
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (a : Rˣ)
local notation "N" => Coordinate (0 : R)
local notation "L" => ZeroTangentOpen (a : R)
local notation "M" => ZeroTangentOpen (-1 : R)
local notation "F" => zeroTangentMobiusForward a
local notation "G" => zeroTangentMobiusBackward a
local notation "A" => algebraMap R L (a : R)
local notation "Ai" => algebraMap R L (Units.val (a⁻¹))

/-- The forward map recovers the unnormalized second coordinate from the target fraction. -/
theorem zeroTangentMobiusForward_fraction :
    F (zeroTangentFraction (-1 : R)) = -Ai * zeroTangentQ (a : R) := by
  have h := congrArg F (zeroTangentFraction_denominator (-1 : R))
  simp only [map_mul, map_sub, zeroTangentMobiusForward_q,
    map_neg, map_one, ← sub_eq_add_neg] at h
  apply (zeroTangentFraction_sub_one_isUnit (a : R) a.isUnit).mul_right_cancel
  rw [h, zeroTangentFraction_sub_one, zeroTangentFraction]
  have hi : Ai * A = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  symm
  calc _ = (Ai * A) * (zeroTangentQ (a : R) *
        ↑((zeroTangent_denominator_isUnit (a : R)).unit⁻¹)) := by ring
    _ = _ := by rw [hi, one_mul]

/-- The reverse map sends the source fraction back to the whole target second coordinate. -/
theorem zeroTangentMobiusBackward_fraction :
    G (zeroTangentFraction (a : R)) = zeroTangentQ (-1 : R) := by
  have h := congrArg G (zeroTangentFraction_denominator (a : R))
  simp only [map_mul, map_add, AlgHom.commutes, zeroTangentMobiusBackward_q] at h
  have hu := (zeroTangent_denominator_isUnit (a : R)).map (G).toRingHom
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_add,
    AlgHom.commutes, zeroTangentMobiusBackward_q] at hu
  apply hu.mul_right_cancel
  rw [h]
  have hd := zeroTangentFraction_denominator (-1 : R)
  simp only [map_neg, map_one] at hd
  linear_combination algebraMap R M (a : R) * hd

/-- The forward map followed algebraically by the reverse fixes the whole source open. -/
theorem zeroTangentMobiusForward_backward : (F).comp G = AlgHom.id R L := by
  apply IsLocalization.algHom_ext (Submonoid.powers (q (0 : R) + algebraMap R N (a : R)))
  apply hom_ext
  · change F (G (zeroTangentP (a : R))) = zeroTangentP (a : R)
    rw [zeroTangentMobiusBackward_p, map_mul, AlgHom.commutes, zeroTangentMobiusForward_p,
      ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
  · change F (G (zeroTangentQ (a : R))) = zeroTangentQ (a : R)
    rw [zeroTangentMobiusBackward_q, map_mul, map_neg, AlgHom.commutes,
      zeroTangentMobiusForward_fraction]
    calc _ = (A * Ai) * zeroTangentQ (a : R) := by ring
      _ = _ := by rw [← map_mul, Units.mul_inv, map_one, one_mul]

/-- The reverse composite fixes every function on the target tangent open. -/
theorem zeroTangentMobiusBackward_forward : (G).comp F = AlgHom.id R M := by
  apply IsLocalization.algHom_ext (Submonoid.powers (q (0 : R) + algebraMap R N (-1 : R)))
  apply hom_ext
  · change G (F (zeroTangentP (-1 : R))) = zeroTangentP (-1 : R)
    rw [zeroTangentMobiusForward_p, map_mul, AlgHom.commutes, zeroTangentMobiusBackward_p,
      ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  · change G (F (zeroTangentQ (-1 : R))) = zeroTangentQ (-1 : R)
    rw [zeroTangentMobiusForward_q, zeroTangentMobiusBackward_fraction]

/-- The entire D(q+a) node has fractional coordinates on the entire D(q-1) node. -/
def zeroTangentMobiusEquiv : M ≃ₐ[R] L :=
  AlgEquiv.ofAlgHom F G (zeroTangentMobiusForward_backward a)
    (zeroTangentMobiusBackward_forward a)

/-- The full equivalence retains the normalized first coordinate. -/
@[simp] theorem zeroTangentMobiusEquiv_p :
    zeroTangentMobiusEquiv a (zeroTangentP (-1 : R)) = Ai * zeroTangentP (a : R) :=
  zeroTangentMobiusForward_p a

/-- The full equivalence retains the fractional second coordinate. -/
@[simp] theorem zeroTangentMobiusEquiv_q :
    zeroTangentMobiusEquiv a (zeroTangentQ (-1 : R)) = zeroTangentFraction (a : R) :=
  zeroTangentMobiusForward_q a

end FLT.Mazur.NodalFiber
