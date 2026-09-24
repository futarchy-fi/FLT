/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Data.ZMod.Basic

/-!
# Full rational two-torsion on the Frey curve

The points `(0, 0)` and `(a^p/4, -a^p/8)` on the normalized Frey model
are distinct nonzero points killed by two. They generate an embedded copy
of `ZMod 2 × ZMod 2` in the rational points.
-/

@[expose] public section

open WeierstrassCurve
open scoped WeierstrassCurve.Affine

/-- Two distinct nonzero points killed by two generate a copy of `(ℤ/2ℤ)²`. -/
theorem fullTwoTorsion_of_two_points {A : Type*} [AddCommGroup A]
    (P Q : A) (hP : P + P = 0) (hQ : Q + Q = 0)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) (hPQ : P ≠ Q) :
    ∃ f : (ZMod 2 × ZMod 2) →+ A, Function.Injective f := by
  let gP : ℤ →+ A :=
    { toFun := fun n => n • P
      map_zero' := by simp
      map_add' := fun m n => add_zsmul P m n }
  let gQ : ℤ →+ A :=
    { toFun := fun n => n • Q
      map_zero' := by simp
      map_add' := fun m n => add_zsmul Q m n }
  let φP : ZMod 2 →+ A := ZMod.lift 2 ⟨gP, by simpa [gP, two_zsmul] using hP⟩
  let φQ : ZMod 2 →+ A := ZMod.lift 2 ⟨gQ, by simpa [gQ, two_zsmul] using hQ⟩
  have hφP : φP 1 = P := by
    rw [show (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) by norm_num]
    simp only [φP, ZMod.lift_coe, gP, AddMonoidHom.coe_mk, ZeroHom.coe_mk, one_zsmul]
  have hφQ : φQ 1 = Q := by
    rw [show (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) by norm_num]
    simp only [φQ, ZMod.lift_coe, gQ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, one_zsmul]
  have hsum : P + Q ≠ 0 := by
    intro h
    exact hPQ ((eq_neg_iff_add_eq_zero.mpr h).trans (neg_eq_iff_add_eq_zero.mpr hQ))
  refine ⟨φP.coprod φQ, (injective_iff_map_eq_zero _).mpr ?_⟩
  rintro ⟨x, y⟩ h
  have cases₂ : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases cases₂ x with rfl | rfl <;> rcases cases₂ y with rfl | rfl
  · rfl
  all_goals simp [AddMonoidHom.coprod_apply, hφP, hφQ, hP0, hQ0, hsum] at h

/-- The normalized Frey curve has full rational two-torsion. -/
theorem FreyPackage.frey_full_two_torsion (P : FreyPackage) :
    ∃ f : (ZMod 2 × ZMod 2) →+ (P.freyCurve⁄ℚ).Point,
      Function.Injective f := by
  have : (P.freyCurve⁄ℚ).IsElliptic :=
    inferInstanceAs ((P.freyCurve.map (algebraMap ℚ ℚ)).IsElliptic)
  have h₀ : (P.freyCurve⁄ℚ).Nonsingular 0 0 := by
    apply (Affine.equation_iff_nonsingular (W := P.freyCurve⁄ℚ)).mp
    rw [Affine.equation_iff]
    simp [FreyPackage.freyCurve, baseChange, map]
  have h₁ : (P.freyCurve⁄ℚ).Nonsingular ((P.a : ℚ) ^ P.p / 4)
      (-((P.a : ℚ) ^ P.p) / 8) := by
    apply (Affine.equation_iff_nonsingular (W := P.freyCurve⁄ℚ)).mp
    rw [Affine.equation_iff]
    simp [FreyPackage.freyCurve, baseChange, map]
    ring
  let T₀ : (P.freyCurve⁄ℚ).Point := .some 0 0 h₀
  let T₁ : (P.freyCurve⁄ℚ).Point := .some _ _ h₁
  have hT₀ : T₀ + T₀ = 0 := by
    apply Affine.Point.add_self_of_Y_eq
    simp [FreyPackage.freyCurve, baseChange, map, Affine.negY]
  have hT₁ : T₁ + T₁ = 0 := by
    apply Affine.Point.add_self_of_Y_eq
    simp [FreyPackage.freyCurve, baseChange, map, Affine.negY]
    ring
  refine fullTwoTorsion_of_two_points T₀ T₁ hT₀ hT₁
    (Affine.Point.some_ne_zero h₀) (Affine.Point.some_ne_zero h₁) ?_
  intro h
  have hx : (0 : ℚ) = (P.a : ℚ) ^ P.p / 4 := (Affine.Point.some.inj h).1
  have ha : (P.a : ℚ) ^ P.p ≠ 0 := pow_ne_zero _ (by exact_mod_cast P.ha0)
  exact (div_ne_zero ha (by norm_num)) hx.symm
