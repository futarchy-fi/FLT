/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberTangentCoefficientMap
public import FLT.Mazur.NodalFiberTangentMobiusEquiv

/-!
# The full fractional smoothing isomorphism follows coefficient restriction

The correction term and the fractional denominator commute with the original
coefficient homomorphism. The square is an equality on every localized function.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.NodalFiber
set_option backward.isDefEq.respectTransparency false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
  (s t : R) (a : Rˣ) (hs : s = (a : R) ^ 2 * t)
  (s' t' : S) (hs' : f s = s') (ht' : f t = t')
local notation "a'" => Units.map f.toMonoidHom a

include hs hs' ht' in
/-- The square of the tangent scale retains the actual target smoothing constant. -/
theorem tangentMobius_smoothing_map : s' = (a' : S) ^ 2 * t' := by
  rw [← hs', hs, map_mul, map_pow, ht']
  rfl

local notation "h'" => tangentMobius_smoothing_map f s t a hs s' t' hs' ht'
local notation "F" => tangentMobiusForward s t a hs
local notation "F'" => tangentMobiusForward s' t' a' h'
local notation "C" => tangentCoefficientRingMap f s (a : R) s' (a' : S) hs' rfl
local notation "D" => tangentCoefficientRingMap f t (-1 : R) t' (-1 : S) ht' (by simp)

/-- The complete fractional isomorphism commutes with independently named target coefficients. -/
theorem tangentMobiusForward_coefficients :
    (C).comp (F).toRingHom = (F').toRingHom.comp D := by
  apply tangent_ringHom_ext
  · intro z
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes, tangentCoefficientRingMap_scalar]
  · change C (F (tangentP t (-1 : R))) = F' (D (tangentP t (-1 : R)))
    rw [tangentMobiusForward_p, map_add, map_mul,
      tangentCoefficientRingMap_scalar, tangentCoefficientRingMap_scalar,
      tangentCoefficientRingMap_p, tangentCoefficientRingMap_p, tangentMobiusForward_p]
    rw [ht']
    rfl
  · change C (F (tangentQ t (-1 : R))) = F' (D (tangentQ t (-1 : R)))
    rw [tangentMobiusForward_q, tangentCoefficientRingMap_fraction,
      tangentCoefficientRingMap_q, tangentMobiusForward_q]

/-- The inverse coordinate change follows the same full coefficient restriction. -/
theorem tangentMobiusBackward_coefficients :
    (D).comp (tangentMobiusBackward s t a hs).toRingHom =
      (tangentMobiusBackward s' t' a' h').toRingHom.comp C := by
  apply tangent_ringHom_ext
  · intro z
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes, tangentCoefficientRingMap_scalar]
  · change D (tangentMobiusBackward s t a hs (tangentP s (a : R))) =
      tangentMobiusBackward s' t' a' h' (C (tangentP s (a : R)))
    rw [tangentMobiusBackward_p, map_mul, map_sub,
      tangentCoefficientRingMap_scalar, tangentCoefficientRingMap_scalar,
      tangentCoefficientRingMap_p, tangentCoefficientRingMap_p, tangentMobiusBackward_p]
    rw [ht']
    rfl
  · change D (tangentMobiusBackward s t a hs (tangentQ s (a : R))) =
      tangentMobiusBackward s' t' a' h' (C (tangentQ s (a : R)))
    simp only [tangentMobiusBackward_q, map_mul, map_neg, tangentCoefficientRingMap_scalar,
      tangentCoefficientRingMap_fraction, tangentCoefficientRingMap_q, tangentMobiusBackward_q]
    rfl

end FLT.Mazur.NodalFiber
