/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.Infinity
public import FLT.EllipticCurve.TorsionFunction
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Point orders of torsion functions

The norm degree bounds affine ideal-power orders, so every nonzero regular
function has a largest such order at each nonsingular affine point. Together
with the valuation at infinity, these orders give exactly `n[P] - n[O]` for a
function generating the nth power of the ideal of P.

The final equality concerns the order function on rational nonsingular
points. This file does not construct divisor pullback or local valuations
at affine points for arbitrary rational functions.
-/

@[expose] public section

open Polynomial
namespace WeierstrassCurve.Affine.CoordinateRing
variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F}
/-- Membership in the mth power of a nonsingular point ideal forces m to be
at most the polynomial norm degree of a nonzero function. -/
theorem pow_le_natDegree_norm_of_mem {x y : F} (h : W.Nonsingular x y)
    {f : W.CoordinateRing} (hf0 : f ≠ 0) {m : ℕ} (hf : f ∈ XYIdeal W x (C y) ^ m) :
    m ≤ (Algebra.norm F[X] f).natDegree := by
  have hg : negHom W f ∈ XYIdeal W x (C (W.negY x y)) ^ m := by
    rw [← map_negHom_XYIdeal, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hf
  have hm := Ideal.mul_mem_mul hg hf
  rw [← mul_pow, XYIdeal_neg_mul h, XIdeal, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hm
  rw [mul_comm, mul_negHom] at hm
  have hd := map_dvd (Algebra.norm F[X]) hm
  rw [Algebra.norm_algebraMap_of_basis (CoordinateRing.basis W), map_pow] at hd
  have hx : Algebra.norm F[X] (XClass W x) = (X - C x) ^ 2 := by
    exact Algebra.norm_algebraMap_of_basis (CoordinateRing.basis W) (X - C x)
  rw [hx] at hd
  have hb := natDegree_le_of_dvd hd (pow_ne_zero _
    ((Algebra.norm_eq_zero_iff_of_basis (CoordinateRing.basis W)).not.mpr hf0))
  simp only [natDegree_pow, natDegree_X_sub_C, mul_one, Fintype.card_fin] at hb
  omega
/-- The affine order of a regular function, measured by powers of the point ideal.
For nonzero functions at nonsingular points the defining set is bounded. -/
noncomputable def affineOrder (f : W.CoordinateRing) (x y : F) : ℕ :=
  sSup {m : ℕ | f ∈ XYIdeal W x (C y) ^ m}

/-- A nonzero regular function belongs to the power defining its affine order. -/
theorem mem_pow_affineOrder {x y : F} (h : W.Nonsingular x y)
    {f : W.CoordinateRing} (hf0 : f ≠ 0) :
    f ∈ XYIdeal W x (C y) ^ affineOrder f x y := by
  have hs : Set.Nonempty {m : ℕ | f ∈ XYIdeal W x (C y) ^ m} := ⟨0, by simp⟩
  exact hs.csSup_mem ((Set.finite_Iic _).subset fun _ hm => pow_le_natDegree_norm_of_mem h hf0 hm)

/-- Ideal-power membership characterizes the affine order of a nonzero function. -/
theorem mem_XYIdeal_pow_iff_le_affineOrder {x y : F} (h : W.Nonsingular x y)
    {f : W.CoordinateRing} (hf0 : f ≠ 0) (m : ℕ) :
    f ∈ XYIdeal W x (C y) ^ m ↔ m ≤ affineOrder f x y := by
  constructor
  · intro hm
    exact le_csSup ⟨(Algebra.norm F[X] f).natDegree,
      fun _ hi => pow_le_natDegree_norm_of_mem h hf0 hi⟩ hm
  · intro hm
    exact Ideal.pow_le_pow_right hm (mem_pow_affineOrder h hf0)

/-- A torsion function has affine order n at its supporting point. -/
theorem affineOrder_torsionFunction {x y : F} (h : W.Nonsingular x y) {n : ℕ}
    {f : W.CoordinateRing} (hf0 : f ≠ 0)
    (hf : XYIdeal W x (C y) ^ n = Ideal.span {f}) : affineOrder f x y = n := by
  apply le_antisymm
  · exact (mem_XYIdeal_pow_iff_of_torsionFunction h hf _).mp (mem_pow_affineOrder h hf0)
  · exact (mem_XYIdeal_pow_iff_le_affineOrder h hf0 n).mp
      ((mem_XYIdeal_pow_iff_of_torsionFunction h hf n).mpr le_rfl)

/-- A torsion function has affine order zero at every other nonsingular affine point. -/
theorem affineOrder_other_torsionFunction {x y x' y' : F}
    (h : W.Nonsingular x' y') (hne : ¬(x = x' ∧ y = y')) {n : ℕ}
    {f : W.CoordinateRing} (hf0 : f ≠ 0)
    (hf : XYIdeal W x (C y) ^ n = Ideal.span {f}) : affineOrder f x' y' = 0 :=
  (mem_other_XYIdeal_pow_iff_of_torsionFunction h.1 hne hf _).mp (mem_pow_affineOrder h hf0)

/-- The pointwise order of a regular function: affine ideal-power order at
finite points and negative logarithmic valuation at infinity. -/
noncomputable def pointOrder (f : W.CoordinateRing) : W.Point → ℤ
  | .zero => -WithZero.log (infinityValuation W f)
  | .some x y _ => affineOrder f x y

/-- All point orders of a torsion function are the coefficients of n[P] - n[O].
This gives its finitely supported order function without a global divisor API. -/
theorem pointOrder_torsionFunction {x y : F} (h : W.Nonsingular x y) {n : ℕ}
    {f : W.CoordinateRing} (hf0 : f ≠ 0)
    (hf : XYIdeal W x (C y) ^ n = Ideal.span {f}) :
    pointOrder f = ⇑(Finsupp.single (Point.some x y h) (n : ℤ) -
      Finsupp.single Point.zero (n : ℤ) : W.Point →₀ ℤ) := by
  classical
  funext Q
  cases Q with
  | zero =>
    simp [pointOrder, infinityValuation_apply_of_ne_zero hf0, natDegree_norm_torsionFunction h hf]
  | some u v hu =>
    by_cases he : x = u ∧ y = v
    · obtain ⟨rfl, rfl⟩ := he
      simp [pointOrder, affineOrder_torsionFunction h hf0 hf]
    · have hP : Point.some x y h ≠ Point.some u v hu := fun hh => he (Point.some.inj hh)
      simp [pointOrder, affineOrder_other_torsionFunction hu he hf0 hf, Ne.symm hP]

end WeierstrassCurve.Affine.CoordinateRing
