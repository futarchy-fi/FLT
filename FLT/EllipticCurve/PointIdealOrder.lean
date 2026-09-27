/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CoordinateRingDedekind
public import FLT.EllipticCurve.PointDivisor
public import FLT.EllipticCurve.PointOrder
public import FLT.Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Local orders of rational functions on elliptic curves

Affine point ideals exhaust the height-one spectrum over an algebraically
closed field. Their multiplicities determine nonzero fractional ideals.
The point order on the function field combines these affine orders with the
valuation at infinity, and extends the existing order of regular functions.
-/

@[expose] public section

open Polynomial IsDedekindDomain
open scoped nonZeroDivisors
namespace WeierstrassCurve.Affine.CoordinateRing
variable {F : Type*} [Field F] [IsAlgClosed F] {W : Affine F} [W.IsElliptic]
/-- The height-one prime defined by a nonsingular affine point. -/
noncomputable def pointSpectrum {x y : F} (h : W.Nonsingular x y) :
    HeightOneSpectrum W.CoordinateRing where
  asIdeal := XYIdeal W x (C y)
  isPrime := (isMaximal_XYIdeal h.1).isPrime
  ne_bot := by
    intro he
    have hm : XClass W x ∈ XYIdeal W x (C y) := Ideal.subset_span (by simp)
    rw [he, Ideal.mem_bot] at hm
    exact XClass_ne_zero x hm

/-- Every height-one prime is the ideal of an affine rational point. -/
theorem exists_eq_pointSpectrum (v : HeightOneSpectrum W.CoordinateRing) :
    ∃ x y, ∃ h : W.Nonsingular x y, v = pointSpectrum h := by
  obtain ⟨x, y, he, hv⟩ := exists_eq_XYIdeal_of_isMaximal v.asIdeal
  exact ⟨x, y, W.equation_iff_nonsingular.mp he, HeightOneSpectrum.ext hv⟩

omit [IsAlgClosed F] [W.IsElliptic] in
/-- Two point primes agree exactly when both affine coordinates agree. -/
theorem pointSpectrum_eq_iff {x y u v : F} (h : W.Nonsingular x y)
    (h' : W.Nonsingular u v) : pointSpectrum h = pointSpectrum h' ↔ x = u ∧ y = v := by
  constructor
  · intro he
    exact (XYIdeal_le_XYIdeal_iff h'.1).mp (congrArg HeightOneSpectrum.asIdeal he).le
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Nonzero fractional ideals are equal when their orders agree at all affine points. -/
theorem fractionalIdeal_ext {I J : FractionalIdeal W.CoordinateRing⁰ W.FunctionField}
    (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ x y, ∀ hp : W.Nonsingular x y,
      FractionalIdeal.count W.FunctionField (pointSpectrum hp) I =
        FractionalIdeal.count W.FunctionField (pointSpectrum hp) J) : I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' W.FunctionField hI,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' W.FunctionField hJ]
  apply finprod_congr
  intro v
  obtain ⟨x, y, hp, rfl⟩ := exists_eq_pointSpectrum v
  rw [h x y hp]

/-- On a nonzero regular function, prime multiplicity agrees with the
largest power of the point ideal containing the function. -/
theorem count_spanSingleton_algebraMap {x y : F} (h : W.Nonsingular x y)
    {f : W.CoordinateRing} (hf : f ≠ 0) :
    FractionalIdeal.count W.FunctionField (pointSpectrum h)
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (algebraMap W.CoordinateRing W.FunctionField f)) = affineOrder f x y := by
  rw [← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe _ _ (by simpa using hf)]
  apply congrArg (fun m : ℕ => (m : ℤ))
  apply le_antisymm
  · apply (mem_XYIdeal_pow_iff_le_affineOrder h hf _).mp
    apply ((pointSpectrum h).intValuation_le_pow_iff_mem f _).mp
    rw [(pointSpectrum h).intValuation_if_neg hf]
  · have hv := ((pointSpectrum h).intValuation_le_pow_iff_mem f _).mpr
      (mem_pow_affineOrder h hf)
    rw [(pointSpectrum h).intValuation_if_neg hf, WithZero.exp_le_exp,
      neg_le_neg_iff, Int.ofNat_le] at hv
    exact hv

variable [DecidableEq F]
/-- A point ideal has multiplicity one at that point and zero at other affine points. -/
theorem count_fractionalIdeal {x y : F} (h : W.Nonsingular x y) (P : W.Point) :
    FractionalIdeal.count W.FunctionField (pointSpectrum h)
      (P.fractionalIdeal : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) =
      if P = Point.some x y h then 1 else 0 := by
  classical
  cases P with
  | zero => simp [Point.fractionalIdeal, FractionalIdeal.count_one]
  | some u v h' =>
    rw [Point.fractionalIdeal_some, XYIdeal'_eq]
    change FractionalIdeal.count W.FunctionField (pointSpectrum h)
      ((pointSpectrum h').asIdeal : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) = _
    rw [FractionalIdeal.count_maximal]
    simp only [pointSpectrum_eq_iff, Point.some.injEq]

end WeierstrassCurve.Affine.CoordinateRing

namespace WeierstrassCurve.Affine.FunctionField
open CoordinateRing
variable {F : Type*} [Field F] [IsAlgClosed F] {W : Affine F} [W.IsElliptic]
/-- The order of a rational function at every nonsingular point, using affine
prime multiplicities and the valuation at infinity. The zero function has order zero. -/
noncomputable def pointOrder (f : W.FunctionField) : W.Point → ℤ
  | .zero => -WithZero.log (infinityValuation W f)
  | .some _ _ h => FractionalIdeal.count W.FunctionField (pointSpectrum h)
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰ f)

/-- At an affine point, rational-function order is the negative logarithm
of the corresponding adic valuation. -/
theorem pointOrder_some {x y : F} (h : W.Nonsingular x y) (f : W.FunctionField) :
    pointOrder f (.some x y h) =
      -WithZero.log ((pointSpectrum h).valuation W.FunctionField f) :=
  (pointSpectrum h).count_spanSingleton_eq_neg_log f

/-- The rational-function order extends the order of nonzero regular functions. -/
theorem pointOrder_algebraMap {f : W.CoordinateRing} (hf : f ≠ 0) :
    pointOrder (algebraMap W.CoordinateRing W.FunctionField f) =
      CoordinateRing.pointOrder f := by
  funext P
  cases P with
  | zero => exact congrArg (fun v => -WithZero.log v) (infinityValuation_algebraMap W f)
  | some x y h => exact count_spanSingleton_algebraMap h hf

/-- A torsion function has full point order n[P] - n[O], now in the function field. -/
theorem pointOrder_torsionFunction {x y : F} (h : W.Nonsingular x y) {n : ℕ}
    {f : W.CoordinateRing} (hf0 : f ≠ 0)
    (hf : XYIdeal W x (C y) ^ n = Ideal.span {f}) :
    pointOrder (algebraMap W.CoordinateRing W.FunctionField f) =
      ⇑(Finsupp.single (Point.some x y h) (n : ℤ) -
        Finsupp.single Point.zero (n : ℤ) : W.Point →₀ ℤ) := by
  rw [pointOrder_algebraMap hf0]
  exact CoordinateRing.pointOrder_torsionFunction h hf0 hf

/-- Orders of nonzero rational functions add under multiplication. -/
theorem pointOrder_mul {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) (P : W.Point) :
    pointOrder (f * g) P = pointOrder f P + pointOrder g P := by
  cases P with
  | zero =>
    simp only [pointOrder, map_mul, WithZero.log_mul
      ((_root_.map_ne_zero (infinityValuation W)).mpr hf)
      ((_root_.map_ne_zero (infinityValuation W)).mpr hg), neg_add_rev]
    omega
  | some x y h =>
    simp only [pointOrder, ← FractionalIdeal.spanSingleton_mul_spanSingleton]
    exact FractionalIdeal.count_mul W.FunctionField (pointSpectrum h)
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hf)
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hg)

/-- Inverting a rational function negates its point orders. -/
theorem pointOrder_inv (f : W.FunctionField) (P : W.Point) :
    pointOrder f⁻¹ P = -pointOrder f P := by
  cases P with
  | zero => simp [pointOrder, map_inv₀, WithZero.log_inv]
  | some x y h =>
    simp only [pointOrder, ← FractionalIdeal.spanSingleton_inv]
    exact FractionalIdeal.count_inv W.FunctionField (pointSpectrum h)
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰ f)
end WeierstrassCurve.Affine.FunctionField
