/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFiberConic
public import Mathlib.RingTheory.Localization.Away.Basic
/-!
# A rational parameter on the first conic neighborhood

On the actual conic open v+a invertible, put z=t/(v+a). Its equation gives
(1-c*z²)*(v+a)=a. For unit a the parameter therefore defines a map from the
localization of the polynomial line at 1-c*X². The two tangent opens cover the
conic. An inverse to the parameter map and smoothness are separate steps.
-/

@[expose] public noncomputable section

open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (a c : R)
/-- The actual conic neighborhood where the opposite tangent factor is invertible. -/
abbrev ConicFirstOpen := Localization.Away (conicV a c + algebraMap R _ a)
/-- The rational parameter t/(v+a) on the actual conic neighborhood. -/
def conicFirstParameter : ConicFirstOpen a c :=
  algebraMap (ConicCoordinate a c) _ (conicT a c) *
    IsLocalization.Away.invSelf (conicV a c + algebraMap R _ a)
local notation "C₀" => ConicCoordinate a c
local notation "O" => ConicFirstOpen a c
local notation "U" => algebraMap C₀ O (conicV a c + algebraMap R C₀ a)
local notation "T" => algebraMap C₀ O (conicT a c)
local notation "V" => algebraMap C₀ O (conicV a c)
local notation "A" => algebraMap R O a
local notation "C" => algebraMap R O c
local notation "z" => conicFirstParameter a c

/-- The parameter multiplied by the original denominator recovers incidence. -/
theorem conicFirstParameter_mul : z * U = T := by
  rw [conicFirstParameter]
  calc (T * IsLocalization.Away.invSelf (conicV a c + algebraMap R C₀ a)) * U =
      T * (U * IsLocalization.Away.invSelf (conicV a c + algebraMap R C₀ a)) := by ring
    _ = T := by rw [IsLocalization.Away.mul_invSelf, mul_one]

/-- The conic equation gives the exact rational-parameter denominator identity. -/
theorem conicFirstParameter_denominator_mul : (1 - C * z ^ 2) * U = A := by
  have hr : V * U = C * T ^ 2 := by
    have h := congrArg (algebraMap C₀ O) (conic_relation a c)
    simpa only [map_sub, map_mul, map_pow, map_zero,
      ← IsScalarTower.algebraMap_apply R C₀ O, sub_eq_zero] using h
  have hv : V = C * z ^ 2 * U := by
    apply (IsLocalization.Away.algebraMap_isUnit
      (S := O) (conicV a c + algebraMap R C₀ a)).mul_right_cancel
    calc V * U = C * T ^ 2 := hr
      _ = (C * z ^ 2 * U) * U := by rw [← conicFirstParameter_mul]; ring
  calc (1 - C * z ^ 2) * U = U - V := by rw [hv]; ring
    _ = A := by
      rw [map_add, ← IsScalarTower.algebraMap_apply R C₀ O]
      ring

/-- A unit tangent coefficient makes the parameter denominator invertible. -/
theorem conicFirstParameter_denominator_isUnit (ha : IsUnit a) :
    IsUnit (1 - C * z ^ 2) := by
  have h : IsUnit ((1 - C * z ^ 2) * U) := by
    rw [conicFirstParameter_denominator_mul]
    exact ha.map (algebraMap R O)
  exact isUnit_of_mul_isUnit_left h

/-- The two oriented tangent neighborhoods cover the entire conic. -/
theorem conic_tangent_opens_cover (ha : IsUnit a) (p : PrimeSpectrum C₀) :
    conicV a c + algebraMap R C₀ a ∉ p.asIdeal ∨ conicV a c ∉ p.asIdeal := by
  by_cases hv : conicV a c ∈ p.asIdeal
  · left
    intro hu
    have h : algebraMap R C₀ a ∈ p.asIdeal := by
      simpa only [add_sub_cancel_left] using p.asIdeal.sub_mem hu hv
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (ha.map (algebraMap R C₀)))
  · exact Or.inr hv

/-- The polynomial denominator of the rational parameter chart. -/
def conicParameterPolynomial : R[X] := 1 - Polynomial.C c * Polynomial.X ^ 2
/-- The candidate parameter line with its denominator inverted. -/
abbrev ConicParameterOpen := Localization.Away (conicParameterPolynomial c)

/-- The proved parameter defines a map to the actual conic neighborhood. -/
def conicParameterToFirst (ha : IsUnit a) : ConicParameterOpen c →ₐ[R] O :=
  IsLocalization.Away.liftAlgHom (f := aeval z) (conicParameterPolynomial c) (by
    simpa only [conicParameterPolynomial, map_sub, map_one, map_mul, map_pow,
      aeval_C, aeval_X] using conicFirstParameter_denominator_isUnit a c ha)

/-- The localized map agrees with evaluation at the actual rational parameter. -/
theorem conicParameterToFirst_base (ha : IsUnit a) (p : R[X]) :
    conicParameterToFirst a c ha (algebraMap R[X] (ConicParameterOpen c) p) =
    aeval z p := by
  rw [conicParameterToFirst, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl
end FLT.Mazur.WeierstrassModificationX
