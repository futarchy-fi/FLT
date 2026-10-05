/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The integral Weierstrass power series at infinity

Solve the infinity-chart equation over any coefficient ring. Hensel lifting is
applied to a monic reciprocal cubic at the simple root one in R[[T]]/(T).
The resulting s(T) is T³ times a unit with constant coefficient one.
This is the coordinate series, not yet the formal addition or multiplication law.
-/

@[expose] public section

namespace FLT.Mazur
open scoped PowerSeries

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The integral infinity-chart equation in the power-series ring. -/
def InfinitySeriesEquation (s : PowerSeries R) : Prop :=
  s = PowerSeries.X ^ 3 + PowerSeries.C W.a₁ * PowerSeries.X * s +
    PowerSeries.C W.a₂ * PowerSeries.X ^ 2 * s + PowerSeries.C W.a₃ * s ^ 2 +
    PowerSeries.C W.a₄ * PowerSeries.X * s ^ 2 + PowerSeries.C W.a₆ * s ^ 3

/-- The chart equation has an integral solution s(T) = T³v(T), with v(0) = 1. -/
theorem exists_infinitySeries :
    ∃ v : PowerSeries R, PowerSeries.constantCoeff v = 1 ∧
      InfinitySeriesEquation W (PowerSeries.X ^ 3 * v) := by
  classical
  let t : PowerSeries R := PowerSeries.X
  let a : PowerSeries R := 1 - PowerSeries.C W.a₁ * t - PowerSeries.C W.a₂ * t ^ 2
  let b : PowerSeries R := (PowerSeries.C W.a₃ + PowerSeries.C W.a₄ * t) * t ^ 3
  let c : PowerSeries R := PowerSeries.C W.a₆ * t ^ 6
  let f : Polynomial (PowerSeries R) := Polynomial.X ^ 3 - Polynomial.C a * Polynomial.X ^ 2 +
    Polynomial.C b * Polynomial.X + Polynomial.C c
  let I : Ideal (PowerSeries R) := Ideal.span {PowerSeries.X}
  have hf : f.Monic := by unfold f; monicity <;> norm_num
  have h0 : f.eval 1 ∈ I := by
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    simp [f, a, b, c, t]
  have hd : PowerSeries.constantCoeff (f.derivative.eval 1) = 1 := by
    simp [f, a, b, c, t, Polynomial.derivative_pow, Polynomial.derivative_mul]
    simp only [map_ofNat]
    ring
  have hu : IsUnit (Ideal.Quotient.mk I (f.derivative.eval 1)) :=
    ((PowerSeries.isUnit_iff_constantCoeff.mpr (hd ▸ isUnit_one))).map _
  obtain ⟨u, hroot, hmod⟩ := HenselianRing.is_henselian f hf 1 h0 hu
  have hu0 : PowerSeries.constantCoeff u = 1 := by
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_sub, map_one, sub_eq_zero] at hmod
    exact hmod
  let v := PowerSeries.invOfUnit u 1
  have hv : u * v = 1 := PowerSeries.mul_invOfUnit u 1 hu0
  have he : u ^ 3 - a * u ^ 2 + b * u + c = 0 := by
    simpa [Polynomial.IsRoot, f] using hroot
  have hh : 1 - a * v + b * v ^ 2 + c * v ^ 3 = 0 := by
    calc
      _ = (u * v) ^ 3 - a * (u * v) ^ 2 * v + b * (u * v) * v ^ 2 + c * v ^ 3 := by
        rw [hv]
        ring
      _ = (u ^ 3 - a * u ^ 2 + b * u + c) * v ^ 3 := by ring
      _ = 0 := by rw [he, zero_mul]
  refine ⟨v, ?_, ?_⟩
  · exact PowerSeries.constantCoeff_invOfUnit u 1
  · change t ^ 3 * v = t ^ 3 + PowerSeries.C W.a₁ * t * (t ^ 3 * v) +
      PowerSeries.C W.a₂ * t ^ 2 * (t ^ 3 * v) + PowerSeries.C W.a₃ * (t ^ 3 * v) ^ 2 +
      PowerSeries.C W.a₄ * t * (t ^ 3 * v) ^ 2 + PowerSeries.C W.a₆ * (t ^ 3 * v) ^ 3
    dsimp only [a, b, c] at hh
    linear_combination -t ^ 3 * hh

/-- The chosen integral coordinate series at infinity. -/
noncomputable def infinitySeries : PowerSeries R :=
  PowerSeries.X ^ 3 * (exists_infinitySeries W).choose

/-- The constructed series satisfies the actual Weierstrass chart equation. -/
theorem infinitySeries_equation : InfinitySeriesEquation W (infinitySeries W) :=
  (exists_infinitySeries W).choose_spec.2

/-- The coordinate series vanishes to order at least three. -/
theorem X_cube_dvd_infinitySeries : PowerSeries.X ^ 3 ∣ infinitySeries W :=
  ⟨_, rfl⟩

/-- The coordinate series has zero constant coefficient. -/
@[simp] theorem constantCoeff_infinitySeries :
    PowerSeries.constantCoeff (infinitySeries W) = 0 := by
  simp [infinitySeries]

/-- The leading cubic coefficient is one. -/
@[simp] theorem coeff_three_infinitySeries : PowerSeries.coeff 3 (infinitySeries W) = 1 := by
  change PowerSeries.coeff (0 + 3) (PowerSeries.X ^ 3 * (exists_infinitySeries W).choose) = 1
  rw [PowerSeries.coeff_X_pow_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact (exists_infinitySeries W).choose_spec.1

/-- A solution with zero constant coefficient is unique. -/
theorem infinitySeries_unique {s₁ s₂ : PowerSeries R}
    (h₁ : InfinitySeriesEquation W s₁) (h₂ : InfinitySeriesEquation W s₂)
    (h₁0 : PowerSeries.constantCoeff s₁ = 0) (h₂0 : PowerSeries.constantCoeff s₂ = 0) :
    s₁ = s₂ := by
  let d := 1 - PowerSeries.C W.a₁ * PowerSeries.X -
    PowerSeries.C W.a₂ * PowerSeries.X ^ 2 - PowerSeries.C W.a₃ * (s₁ + s₂) -
    PowerSeries.C W.a₄ * PowerSeries.X * (s₁ + s₂) -
    PowerSeries.C W.a₆ * (s₁ ^ 2 + s₁ * s₂ + s₂ ^ 2)
  have hd : IsUnit d := PowerSeries.isUnit_iff_constantCoeff.mpr (by
    simp [d, h₁0, h₂0])
  apply sub_eq_zero.mp
  apply hd.mul_right_eq_zero.mp
  dsimp only [d]
  unfold InfinitySeriesEquation at h₁ h₂
  linear_combination h₁ - h₂

/-- Any zero-constant solution agrees with the constructed coordinate series. -/
theorem eq_infinitySeries {s : PowerSeries R} (hs : InfinitySeriesEquation W s)
    (h0 : PowerSeries.constantCoeff s = 0) : s = infinitySeries W :=
  infinitySeries_unique W hs (infinitySeries_equation W) h0 (constantCoeff_infinitySeries W)

/-- The integral coordinate series commutes with every change of coefficient ring. -/
theorem infinitySeries_map {S : Type*} [CommRing S] (f : R →+* S) :
    PowerSeries.map f (infinitySeries W) = infinitySeries (W.map f) := by
  apply eq_infinitySeries
  · have h := congrArg (PowerSeries.map f) (infinitySeries_equation W)
    simpa [InfinitySeriesEquation] using h
  · change f (PowerSeries.constantCoeff (infinitySeries W)) = 0
    rw [constantCoeff_infinitySeries, map_zero]

end FLT.Mazur
