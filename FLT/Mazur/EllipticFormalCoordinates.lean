/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticInfinityPowerSeries
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Integral formal coordinates in several variables

The infinity equation remains valid after substituting any zero-constant formal
parameter. Its zero-constant solution is unique, over arbitrary coefficient rings.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity

variable {R : Type*} [CommRing R] {σ : Type*}

/-- The Weierstrass equation in the chart [t : -1 : s]. -/
def Equation (W : WeierstrassCurve R) (t s : R) : Prop :=
  s = t ^ 3 + W.a₁ * t * s + W.a₂ * t ^ 2 * s + W.a₃ * s ^ 2 +
    W.a₄ * t * s ^ 2 + W.a₆ * s ^ 3

/-- The coefficient-ring extension to multivariate series. -/
noncomputable abbrev curve (W : WeierstrassCurve R) : WeierstrassCurve (MvPowerSeries σ R) :=
  W.map MvPowerSeries.C

/-- The s-coordinate obtained by formal substitution into the integral series. -/
noncomputable def coordinate (W : WeierstrassCurve R) (t : MvPowerSeries σ R) :
    MvPowerSeries σ R := (infinitySeries W).subst t

/-- A zero-constant parameter gives a zero-constant s-coordinate. -/
@[simp] theorem constantCoeff_coordinate (W : WeierstrassCurve R)
    {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    (coordinate W t).constantCoeff = 0 := by
  exact PowerSeries.constantCoeff_subst_eq_zero ht _ (constantCoeff_infinitySeries W)

/-- Substitution preserves the infinity equation. -/
theorem equation_coordinate (W : WeierstrassCurve R)
    {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    Equation (curve W) t (coordinate W t) := by
  have h := congrArg (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero ht))
    (infinitySeries_equation W)
  simpa [InfinitySeriesEquation, Equation, curve, coordinate,
    map_add, map_mul, map_pow, PowerSeries.substAlgHom_X,
    PowerSeries.coe_substAlgHom, PowerSeries.subst_C] using h

/-- The difference factor whose constant coefficient is one. -/
def differenceUnit (W : WeierstrassCurve R) (t s u : R) : R :=
  1 - W.a₁ * t - W.a₂ * t ^ 2 - W.a₃ * (s + u) -
    W.a₄ * t * (s + u) - W.a₆ * (s ^ 2 + s * u + u ^ 2)

/-- The difference factor is a unit for zero-constant coordinates. -/
theorem isUnit_differenceUnit (W : WeierstrassCurve R) {t s u : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hs : s.constantCoeff = 0) (hu : u.constantCoeff = 0) :
    IsUnit (differenceUnit (curve W) t s u) := by
  apply MvPowerSeries.isUnit_iff_constantCoeff.mpr
  simp [differenceUnit, curve, ht, hs, hu]

/-- The zero-constant solution of the multivariate chart equation is unique. -/
theorem equation_unique (W : WeierstrassCurve R) {t s u : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hs : s.constantCoeff = 0) (hu : u.constantCoeff = 0)
    (h₁ : Equation (curve W) t s) (h₂ : Equation (curve W) t u) : s = u := by
  apply sub_eq_zero.mp
  apply (isUnit_differenceUnit W ht hs hu).mul_right_eq_zero.mp
  unfold differenceUnit
  unfold Equation at h₁ h₂
  linear_combination h₁ - h₂

/-- Every zero-constant chart solution is the substituted integral series. -/
theorem eq_coordinate (W : WeierstrassCurve R) {t s : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hs : s.constantCoeff = 0)
    (h : Equation (curve W) t s) : s = coordinate W t :=
  equation_unique W ht hs (constantCoeff_coordinate W ht) h (equation_coordinate W ht)

end FLT.Mazur.FormalInfinity
