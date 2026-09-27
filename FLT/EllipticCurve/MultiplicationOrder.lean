/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.FiberOrder
public import FLT.EllipticCurve.MultiplicationRoot
public import FLT.EllipticCurve.TorsionFunction
/-!
# Reducing multiplication roots to local order transport

The local orders of the fiber ideal give the fractional-ideal identity once
multiplication pullback preserves point orders. Principality of the fiber
ideal then gives an exact nth root. The local transport hypothesis remains
explicit in both results.
-/

@[expose] public section

open Polynomial
open scoped nonZeroDivisors WeierstrassCurve.Affine
namespace WeierstrassCurve.Affine.FunctionField
variable {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
  (W : Affine F) [W.IsElliptic]
/-- Preservation of affine point orders under multiplication pullback gives
the fractional-ideal identity for a torsion function. -/
theorem span_nsmulPullback_eq_fiberIdeal_of_pointOrder
    {n : ℕ} (hn : n ≠ 0) (Q : W.Point)
    {x y : F} (h : W.Nonsingular x y) (hQ : n • Q = Point.some x y h)
    {f : W.CoordinateRing} (hf0 : f ≠ 0)
    (hf : CoordinateRing.XYIdeal W x (C y) ^ n = Ideal.span {f})
    (htransport : ∀ u v, ∀ hp : W.Nonsingular u v,
      pointOrder (nsmulPullback W n hn (algebraMap W.CoordinateRing W.FunctionField f))
        (Point.some u v hp) =
      pointOrder (algebraMap W.CoordinateRing W.FunctionField f) (n • Point.some u v hp)) :
    FractionalIdeal.spanSingleton W.CoordinateRing⁰
      (nsmulPullback W n hn (algebraMap W.CoordinateRing W.FunctionField f)) =
      (Point.fiberIdeal W n hn Q : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ n := by
  have hfK : nsmulPullback W n hn (algebraMap W.CoordinateRing W.FunctionField f) ≠ 0 :=
    (_root_.map_ne_zero (nsmulPullback W n hn)).mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hf0)
  apply CoordinateRing.fractionalIdeal_ext
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hfK)
    (pow_ne_zero _ (Point.fiberIdeal W n hn Q).ne_zero)
  intro u v hp
  change pointOrder _ (Point.some u v hp) = _
  rw [htransport, FractionalIdeal.count_pow, Point.count_fiberIdeal,
    pointOrder_torsionFunction h hf0 hf, hQ]
  simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply, mul_sub,
    mul_ite, mul_one, mul_zero, eq_comm, Point.zero_def]
/-- Local order transport, torsion-fiber principality, and scalar normalization
produce an exact nth root of the multiplication pullback of a torsion function. -/
theorem exists_pow_eq_nsmulPullback_of_pointOrder {n : ℕ} (hn : n ≠ 0)
    (hchar : (n : F) ≠ 0) {x y : F} (h : W.Nonsingular x y)
    {f : W.CoordinateRing} (hf0 : f ≠ 0)
    (hf : CoordinateRing.XYIdeal W x (C y) ^ n = Ideal.span {f})
    (htransport : ∀ u v, ∀ hp : W.Nonsingular u v,
      pointOrder (nsmulPullback W n hn (algebraMap W.CoordinateRing W.FunctionField f))
        (Point.some u v hp) =
      pointOrder (algebraMap W.CoordinateRing W.FunctionField f) (n • Point.some u v hp)) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      g ^ n = nsmulPullback W n hn (algebraMap W.CoordinateRing W.FunctionField f) := by
  have hT : n • (Point.some x y h : W.Point) = 0 :=
    (Point.nsmul_eq_zero_iff_exists_torsionFunction h n).mpr ⟨f, hf0, hf⟩
  obtain ⟨Q, hQ⟩ := Point.exists_nsmul_eq_of_torsion W hchar _ hT
  apply exists_pow_eq_pullback_of_span_eq_fiberIdeal hn hchar Q (by rw [hQ, hT])
  exact span_nsmulPullback_eq_fiberIdeal_of_pointOrder W hn Q h hQ hf0 hf htransport
end WeierstrassCurve.Affine.FunctionField
