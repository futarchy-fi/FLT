/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingReciprocalScaling
public import FLT.Mazur.PolygonSmoothingRingMap
public import FLT.Mazur.PolygonUniversalScaling

/-!
# Coefficient naturality and a variable reciprocal-scaling parameter

The full arithmetic ring maps commute with arbitrary coefficient changes.
The universal Laurent unit supplies a variable parameter, whose specialization
recovers every coefficient-unit automorphism without discarding nilpotents.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

/-- Original coefficients and the two coordinates determine any ring map. -/
theorem chartRing_ringHom_ext (t : R) (f g : ChartRing t →+* S)
    (hc : ∀ r, f (algebraMap R (ChartRing t) r) = g (algebraMap R (ChartRing t) r))
    (hx : f (leftCoordinate t) = g (leftCoordinate t))
    (hy : f (rightCoordinate t) = g (rightCoordinate t)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · exact hc
  · intro j
    fin_cases j
    · exact hx
    · exact hy

/-- Reciprocal scaling is natural under arbitrary changes of the original coefficients. -/
theorem ringMap_reciprocalScale (f : R →+* S) (t : R) (s : S) (hs : f t = s) (a : Rˣ) :
    (ringMap f t s hs).comp (reciprocalScale t a).toRingHom =
      (reciprocalScale s (Units.map f a)).toRingHom.comp (ringMap f t s hs) := by
  apply chartRing_ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes, ringMap_scalar]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      reciprocalScale_left, ringMap_left, map_mul, ringMap_scalar, Units.coe_map]
    rfl
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      reciprocalScale_right, ringMap_right, map_mul, ringMap_scalar, ← map_inv, Units.coe_map]
    rfl

/-- The universal parameter scales the full smoothing equation over the Laurent coefficients. -/
def universalReciprocalScale (t : R) :
    ChartRing t →+* ChartRing (LaurentPolynomial.C t : R[T;T⁻¹]) :=
  (reciprocalScale (LaurentPolynomial.C t) (PolygonUniversalScaling.u (R := R))).toRingHom.comp
    (ringMap LaurentPolynomial.C t (LaurentPolynomial.C t) rfl)

/-- Specialize the parameter in the entire arithmetic node family. -/
def specializeReciprocalScale (t : R) (a : Rˣ) :
    ChartRing (LaurentPolynomial.C t : R[T;T⁻¹]) →+* ChartRing t :=
  ringMap (LaurentPolynomial.eval₂ (RingHom.id R) a) (LaurentPolynomial.C t) t (by simp)

/-- Specializing the universal parameter recovers the actual original-ring automorphism. -/
theorem specialize_universalReciprocalScale (t : R) (a : Rˣ) :
    (specializeReciprocalScale t a).comp (universalReciprocalScale t) =
      (reciprocalScale t a).toRingHom := by
  apply chartRing_ringHom_ext
  · intro r
    simp [specializeReciprocalScale, universalReciprocalScale]
  · simp [specializeReciprocalScale, universalReciprocalScale,
      PolygonUniversalScaling.specialize_u]
  · simp [specializeReciprocalScale, universalReciprocalScale,
      PolygonUniversalScaling.specialize_u_inv]

end FLT.Mazur.PolygonSmoothing
