/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.PointIdealOrder
public import FLT.EllipticCurve.TorsionFiber

/-!
# Orders of multiplication-fiber ideals

The fractional ideal of the difference of two multiplication fibers has
order one above the target and order minus one above the origin. This
computes the ideal side of the multiplication-pullback comparison.
-/

@[expose] public section

open Polynomial IsDedekindDomain
open scoped nonZeroDivisors
namespace WeierstrassCurve.Affine.Point
open CoordinateRing
variable {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
  {W : Affine F} [W.IsElliptic]
/-- The order of a finite product of point ideals counts occurrences of the given point. -/
theorem count_prod_fractionalIdeal {ι : Type*} (s : Finset ι) (P : ι → W.Point)
    {x y : F} (h : W.Nonsingular x y) :
    FractionalIdeal.count W.FunctionField (pointSpectrum h)
      ((∏ i ∈ s, fractionalIdeal (P i) : (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) =
      ∑ i ∈ s, (if P i = some x y h then 1 else 0 : ℤ) := by
  classical
  simp only [Units.coe_prod]
  rw [FractionalIdeal.count_prod _ _ _ _ (fun i _ => (fractionalIdeal (P i)).ne_zero)]
  simp only [count_fractionalIdeal]

/-- The fiber-difference ideal has orders given by the two fiber indicators. -/
theorem count_fiberIdeal {n : ℕ} (hn : n ≠ 0) (Q : W.Point)
    {x y : F} (h : W.Nonsingular x y) :
    FractionalIdeal.count W.FunctionField (pointSpectrum h)
      (fiberIdeal W n hn Q : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) =
      (if n • some x y h = n • Q then 1 else 0 : ℤ) -
        (if n • some x y h = 0 then 1 else 0 : ℤ) := by
  classical
  unfold fiberIdeal
  rw [Units.val_div_eq_div_val, div_eq_mul_inv,
    FractionalIdeal.count_mul _ _ (Units.ne_zero _) (inv_ne_zero (Units.ne_zero _)),
    FractionalIdeal.count_inv, count_prod_fractionalIdeal, count_prod_fractionalIdeal]
  have he (R : W.Point) : R + Q = some x y h ↔ R = some x y h - Q :=
    eq_sub_iff_add_eq.symm
  simp only [he, Finset.sum_ite_eq', mem_torsionPoints, nsmul_sub, sub_eq_zero]
  rfl
end WeierstrassCurve.Affine.Point

