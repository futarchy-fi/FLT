/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CoordinateRing
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Fractional ideals of point divisors

The origin contributes the unit ideal on the affine curve. Products of the
other point ideals represent finite point divisors restricted to this affine
chart. Such a product is principal exactly when its sum in the elliptic-curve
group is zero. The degree at the omitted origin is not recorded by the ideal.
-/

@[expose] public section

open scoped nonZeroDivisors
namespace WeierstrassCurve.Affine.Point
variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}

/-- The invertible fractional ideal of a point on the affine chart, with the
origin represented by the unit ideal. -/
noncomputable def fractionalIdeal : W.Point → (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ
  | zero => 1
  | some _ _ h => CoordinateRing.XYIdeal' h

omit [DecidableEq F] in
/-- The origin has trivial fractional ideal on the affine chart. -/
@[simp] theorem fractionalIdeal_zero : fractionalIdeal (0 : W.Point) = 1 := rfl

omit [DecidableEq F] in
/-- An affine point is represented by its usual invertible point ideal. -/
@[simp] theorem fractionalIdeal_some {x y : F} (h : W.Nonsingular x y) :
    fractionalIdeal (some x y h) = CoordinateRing.XYIdeal' h := rfl

/-- The class of the point ideal is the class used to define the group law. -/
theorem mk_fractionalIdeal (P : W.Point) :
    ClassGroup.mk W.FunctionField (fractionalIdeal P) = (toClass P).toMul := by
  cases P with
  | zero => exact map_one _
  | some x y h => rfl

omit [DecidableEq F] in
/-- A unit fractional ideal with trivial class has a nonzero rational generator. -/
theorem exists_generator_iff (I : (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ) :
    (∃ g : W.FunctionField, g ≠ 0 ∧
      FractionalIdeal.spanSingleton W.CoordinateRing⁰ g = I) ↔
      ClassGroup.mk W.FunctionField I = 1 := by
  constructor
  · rintro ⟨g, hg, he⟩
    have hp : toPrincipalIdeal W.CoordinateRing W.FunctionField (Units.mk0 g hg) = I :=
      toPrincipalIdeal_eq_iff.mpr he
    have hh := (ClassGroup.mk_eq_mk (I := 1) (J := I)).mpr
      ⟨Units.mk0 g hg, by simpa using hp⟩
    simpa using hh.symm
  · intro hI
    have hh : ClassGroup.mk W.FunctionField 1 = ClassGroup.mk W.FunctionField I := by
      rw [map_one, hI]
    obtain ⟨g, hg⟩ := ClassGroup.mk_eq_mk.mp hh
    refine ⟨g, g.ne_zero, ?_⟩
    apply toPrincipalIdeal_eq_iff.mp
    simpa using hg

/-- The class of a finite product of point ideals is the sum of its points. -/
theorem mk_prod_fractionalIdeal {ι : Type*} (s : Finset ι) (P : ι → W.Point) :
    ClassGroup.mk W.FunctionField (∏ i ∈ s, fractionalIdeal (P i)) =
      (toClass (∑ i ∈ s, P i)).toMul := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi, map_mul, map_add,
      mk_fractionalIdeal, ih]
    rfl

/-- A quotient of products of point ideals has a nonzero rational generator
exactly when the two sums of points agree. -/
theorem exists_generator_div_prod_iff {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (P : ι → W.Point) (Q : κ → W.Point) :
    (∃ g : W.FunctionField, g ≠ 0 ∧
      FractionalIdeal.spanSingleton W.CoordinateRing⁰ g =
        ((∏ i ∈ s, fractionalIdeal (P i)) / (∏ j ∈ t, fractionalIdeal (Q j)) :
          (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ)) ↔
      ∑ i ∈ s, P i = ∑ j ∈ t, Q j := by
  rw [exists_generator_iff, map_div, div_eq_one,
    mk_prod_fractionalIdeal, mk_prod_fractionalIdeal]
  exact Additive.toMul.injective.eq_iff.trans toClass_injective.eq_iff

end WeierstrassCurve.Affine.Point
