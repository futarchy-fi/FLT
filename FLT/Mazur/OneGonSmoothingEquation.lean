/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Tactic.Ring

/-!
# An explicit complete-base smoothing equation for the one-gon

The equation y² - xy = x³ + t specializes to the original split nodal
cubic. Its discriminant is -t(1 + 432t), in every characteristic. Over
power series the second factor is a unit, so every field fiber away from
the parameter-zero locus is elliptic.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.OneGonSmoothing
variable {R S : Type*} [CommRing R] [CommRing S]

/-- The explicit smoothing of the split nodal cubic with its infinity marking. -/
def equation (t : R) : WeierstrassCurve R := ⟨-1, 0, 0, 0, t⟩

/-- The specified smoothing equation commutes with actual coefficient homomorphisms. -/
theorem equation_map (t : R) (f : R →+* S) :
    (equation t).map f = equation (f t) := by
  ext <;> simp [equation, WeierstrassCurve.map]

/-- The c4 invariant is a unit even on the singular fiber. -/
theorem equation_c4 (t : R) : (equation t).c₄ = 1 := by
  simp [equation, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]

/-- The original discriminant has a simple parameter factor in every characteristic. -/
theorem equation_discriminant (t : R) : (equation t).Δ = -t * (1 + 432 * t) := by
  simp only [equation, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- The factor complementary to the parameter is a unit in the actual power-series ring. -/
theorem powerSeries_discriminant_factor_unit :
    IsUnit (1 + 432 * (PowerSeries.X : PowerSeries R)) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  simp

variable (K : Type*) [Field K]

/-- The explicit complete-base cubic has nonzero discriminant. -/
theorem powerSeries_discriminant_ne_zero :
    (equation (PowerSeries.X : PowerSeries K)).Δ ≠ 0 := by
  rw [equation_discriminant]
  exact mul_ne_zero (neg_ne_zero.mpr PowerSeries.X_ne_zero)
    powerSeries_discriminant_factor_unit.ne_zero

/-- Every field-valued coefficient map with nonzero parameter gives an elliptic curve. -/
theorem fieldFiber_isElliptic {L : Type*} [Field L] (f : PowerSeries K →+* L)
    (ht : f PowerSeries.X ≠ 0) : ((equation PowerSeries.X).map f).IsElliptic := by
  constructor
  apply isUnit_iff_ne_zero.mpr
  rw [WeierstrassCurve.map_Δ, equation_discriminant, map_mul, map_neg]
  exact mul_ne_zero (neg_ne_zero.mpr ht)
    (powerSeries_discriminant_factor_unit.map f).ne_zero

end FLT.Mazur.OneGonSmoothing
