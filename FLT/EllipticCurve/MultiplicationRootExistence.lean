/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.MultiplicationOrder
public import FLT.EllipticCurve.TranslationValuation
/-!
# Exact roots of pulled-back torsion functions

Translation identifies all point valuations with the valuation at infinity.
Multiplication by an invertible integer preserves that valuation. Local order
transport then proves the fiber-ideal identity and exact nth-root existence.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine nonZeroDivisors
namespace WeierstrassCurve.Affine.FunctionField
variable {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
  (W : Affine F) [W.IsElliptic]
/-- Multiplication by an invertible integer preserves local orders at every point. -/
theorem pointOrder_nsmulPullback
    {n : ℕ} (hn : n ≠ 0) (hchar : (n : F) ≠ 0) (f : W.FunctionField) (P : W.Point) :
    pointOrder (nsmulPullback W n hn f) P = pointOrder f (n • P) := by
  have horder (g : W.FunctionField) (Q : W.Point) :
      pointOrder g Q = -WithZero.log (infinityValuation W (translationPullback W Q g)) := by
    cases Q with
    | zero => rw [show (Point.zero : W.Point) = 0 from rfl, translationPullback_zero]; rfl
    | some u v h => rw [pointOrder_some, pointValuation_eq_translation]; rfl
  rw [horder, horder]
  have he := congrArg (fun φ : W.FunctionField →ₐ[F] W.FunctionField => φ f)
    (translation_nsmulPullback W n hn P)
  change translationPullback W P (nsmulPullback W n hn f) =
    nsmulPullback W n hn (translationPullback W (n • P) f) at he
  rw [he, infinityValuation_nsmulPullback W hn hchar]
/-- The principal fractional ideal of a pulled-back torsion function is the
nth power of the corresponding multiplication-fiber ideal. -/
theorem span_nsmulPullback_eq_fiberIdeal
    {n : ℕ} (hn : n ≠ 0) (hchar : (n : F) ≠ 0) (Q : W.Point)
    {x y : F} (h : W.Nonsingular x y) (hQ : n • Q = Point.some x y h)
    {f : W.CoordinateRing} (hf0 : f ≠ 0)
    (hf : CoordinateRing.XYIdeal W x (Polynomial.C y) ^ n = Ideal.span {f}) :
    FractionalIdeal.spanSingleton W.CoordinateRing⁰
      (nsmulPullback W n hn (algebraMap W.CoordinateRing W.FunctionField f)) =
      (Point.fiberIdeal W n hn Q : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ n := by
  apply span_nsmulPullback_eq_fiberIdeal_of_pointOrder W hn Q h hQ hf0 hf
  intro u v hp
  exact pointOrder_nsmulPullback W hn hchar _ _

omit [DecidableEq F] in
/-- A torsion function has an exact nth root after multiplication pullback
when n is invertible in the algebraically closed ground field. -/
theorem exists_pow_eq_nsmulPullback {n : ℕ} (hn : n ≠ 0)
    (hchar : (n : F) ≠ 0) {x y : F} (h : W.Nonsingular x y)
    {f : W.CoordinateRing} (hf0 : f ≠ 0)
    (hf : CoordinateRing.XYIdeal W x (Polynomial.C y) ^ n = Ideal.span {f}) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      g ^ n = nsmulPullback W n hn (algebraMap W.CoordinateRing W.FunctionField f) := by
  classical
  apply exists_pow_eq_nsmulPullback_of_pointOrder W hn hchar h hf0 hf
  intro u v hp
  exact pointOrder_nsmulPullback W hn hchar _ _
end WeierstrassCurve.Affine.FunctionField
