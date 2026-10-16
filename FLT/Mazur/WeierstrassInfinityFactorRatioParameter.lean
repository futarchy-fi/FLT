/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityNilpotentIncidence
public import FLT.Mazur.LaurentUnitPoints
public import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-!
# The full factor ratio on the entire original infinity chart

Multiplying both tangent factors by X/Y removes their common pole. Their
quotient is a unit on the entire original infinity chart, with the exact
polynomial root evaluated at the regular extension of the incidence coordinate.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  (I : Ideal R) (hI : IsNilpotent I)
  (h2 : W.a₂ ∈ I) (h3 : W.a₃ ∈ I) (h4 : W.a₄ ∈ I) (h6 : W.a₆ ∈ I)
local notation "B" => Coordinate W 1
local notation "u" => coord W 1 0
local notation "c" => algebraMap R B
local notation "J" => I.map c

include hI h2 h3 h4 h6 in
/-- The linear split denominator stays invertible on the full arithmetic infinity chart. -/
theorem nilpotentInfinityLinear_isUnit : IsUnit (1 + c W.a₁ * u) := by
  have hn : IsNilpotent (nilpotentInfinityDenominator W - (1 + c W.a₁ * u)) :=
    NilpotentQuadraticRoot.element_nilpotent J
      (NilpotentPolynomialInverse.mapIdeal_nilpotent I hI c)
      (nilpotentInfinityDenominator_correction_mem W I h2 h3 h4 h6)
  have hu := hn.neg.isUnit_add_left_of_commute
    (nilpotentInfinityDenominator_isUnit W I hI h2 h3 h4 h6) (mul_comm _ _)
  convert hu using 1
  ring

variable (s b3 : R) (r : R[X]) (hrI : r ∈ I.map Polynomial.C) (hb3 : b3 ∈ I)
local notation "t" => nilpotentInfinityIncidence W I hI h2 h3 h4 h6 s
local notation "v" => Polynomial.eval₂ c t r

/-- The numerator of the original small tangent factor after clearing its pole. -/
def infinitySmallFactor : B := 1 - u * v

/-- The numerator of the original opposite tangent factor after clearing its pole. -/
def infinityOppositeFactor : B := 1 + u * (v + c W.a₁ + c b3 * t)

include hrI in
/-- The small numerator is a unit at every point of the original infinity chart. -/
theorem infinitySmallFactor_isUnit : IsUnit (infinitySmallFactor W I hI h2 h3 h4 h6 s r) := by
  have hn := NilpotentPolynomialInverse.eval₂_nilpotent I c r hrI hI t
  simpa only [infinitySmallFactor, sub_eq_add_neg] using
    ((Commute.all u v).isNilpotent_mul_left hn).neg.isUnit_add_left_of_commute
      isUnit_one (mul_comm _ _)

include hrI hb3 in
/-- The opposite numerator is a unit on the same entire chart, with every correction retained. -/
theorem infinityOppositeFactor_isUnit :
    IsUnit (infinityOppositeFactor W I hI h2 h3 h4 h6 s b3 r) := by
  have hv := NilpotentPolynomialInverse.eval₂_nilpotent I c r hrI hI t
  have hb := (NilpotentQuadraticRoot.element_nilpotent I hI hb3).map c
  have hn := ((Commute.all v (c b3 * t)).isNilpotent_add hv
    ((Commute.all (c b3) t).isNilpotent_mul_right hb))
  have hn' := (Commute.all u (v + c b3 * t)).isNilpotent_mul_left hn
  have hu := hn'.isUnit_add_left_of_commute
    (nilpotentInfinityLinear_isUnit W I hI h2 h3 h4 h6) (mul_comm _ _)
  convert hu using 1
  dsimp only [infinityOppositeFactor]
  ring

/-- The full regular factor ratio on the original chart, including infinity itself. -/
def infinityFactorRatioUnit : Bˣ :=
  (infinitySmallFactor_isUnit W I hI h2 h3 h4 h6 s r hrI).unit *
    (infinityOppositeFactor_isUnit W I hI h2 h3 h4 h6 s b3 r hrI hb3).unit⁻¹

/-- The exact numerator-denominator identity for the full regular ratio. -/
theorem infinityFactorRatioUnit_denominator :
    (infinityFactorRatioUnit W I hI h2 h3 h4 h6 s b3 r hrI hb3 : B) *
      infinityOppositeFactor W I hI h2 h3 h4 h6 s b3 r =
        infinitySmallFactor W I hI h2 h3 h4 h6 s r := by
  rw [infinityFactorRatioUnit, Units.val_mul, mul_assoc,
    (infinityOppositeFactor_isUnit W I hI h2 h3 h4 h6 s b3 r hrI hb3).val_inv_mul,
    mul_one, IsUnit.unit_spec]

/-- The constructed ratio defines a map from the entire original infinity chart to the torus. -/
def infinityFactorRatioParameter : Spec (.of B) ⟶ Spec (.of R[T;T⁻¹]) :=
  Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit
    (infinityFactorRatioUnit W I hI h2 h3 h4 h6 s b3 r hrI hb3)).toRingHom)

end FLT.Mazur.WeierstrassIntegralChart
