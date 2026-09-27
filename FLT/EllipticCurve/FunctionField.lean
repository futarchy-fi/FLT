/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CoordinateRing
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Norm.Basic

/-!
# Evaluation in the function field of a Weierstrass curve

Evaluation at a point whose x-coordinate is transcendental is injective on
the coordinate ring, so it extends to the function field.
-/

@[expose] public section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine.CoordinateRing

variable {F L : Type*} [Field F] [Field L] {W : WeierstrassCurve.Affine F}

/-- A homomorphism out of the coordinate ring is injective if its restriction
to the polynomial ring in x is injective. The norm detects its kernel. -/
theorem injective_of_injective_polynomial (φ : W.CoordinateRing →+* L)
    (hφ : Function.Injective (φ.comp (algebraMap F[X] W.CoordinateRing))) :
    Function.Injective φ := by
  apply (injective_iff_map_eq_zero φ).mpr
  intro f hf
  apply (Algebra.norm_eq_zero_iff_of_basis (CoordinateRing.basis W)).mp
  apply (injective_iff_map_eq_zero (φ.comp (algebraMap F[X] W.CoordinateRing))).mp hφ
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq f
  change φ (algebraMap F[X] W.CoordinateRing (Algebra.norm F[X] _)) = 0
  have he : mk W (C p) + mk W (C q) * mk W Y = p • 1 + q • mk W Y := by
    simp only [Algebra.smul_def, mul_one]
    rfl
  have hn : algebraMap F[X] W.CoordinateRing (Algebra.norm F[X] (p • 1 + q • mk W Y)) =
      (p • 1 + q • mk W Y) *
        mk W (C p + C q * (-(Y : F[X][Y]) - C (C W.a₁ * X + C W.a₃))) := by
    rw [AdjoinRoot.algebraMap_eq, coe_norm_smul_basis, map_mul]
    congr 1
  rw [hn, map_mul, hf, zero_mul]

variable [Algebra F L]

/-- Evaluation at a point over an extension field, as an algebra homomorphism. -/
noncomputable def evalAt {x y : L} (h : (W.map (algebraMap F L)).Equation x y) :
    W.CoordinateRing →ₐ[F] L :=
  AdjoinRoot.liftAlgHom W.polynomial (aeval x) y (by
    change W.polynomial.eval₂ (eval₂RingHom (algebraMap F L) x) y = 0
    rw [eval₂_eval₂RingHom_apply, ← map_polynomial]
    exact h)

/-- Evaluation on the polynomial subring is ordinary polynomial evaluation. -/
theorem evalAt_polynomial {x y : L} (h : (W.map (algebraMap F L)).Equation x y)
    (p : F[X]) : evalAt h (algebraMap F[X] W.CoordinateRing p) = aeval x p := by
  exact AdjoinRoot.liftAlgHom_of _ _ _ _ _

/-- Evaluation sends the y-coordinate to the specified y-coordinate. -/
theorem evalAt_Y {x y : L} (h : (W.map (algebraMap F L)).Equation x y) :
    evalAt h (mk W Y) = y := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

/-- Evaluation at a point with transcendental x-coordinate is injective. -/
theorem evalAt_injective {x y : L} (h : (W.map (algebraMap F L)).Equation x y)
    (hx : Transcendental F x) : Function.Injective (evalAt h) := by
  apply injective_of_injective_polynomial (evalAt h).toRingHom
  intro p q he
  apply (transcendental_iff_injective.mp hx)
  change evalAt h (algebraMap F[X] W.CoordinateRing p) =
    evalAt h (algebraMap F[X] W.CoordinateRing q) at he
  simpa only [evalAt_polynomial] using he

/-- Evaluation at a point with transcendental x-coordinate extends to all
rational functions on the curve. -/
noncomputable def evalFunctionField {x y : L}
    (h : (W.map (algebraMap F L)).Equation x y) (hx : Transcendental F x) :
    W.FunctionField →ₐ[F] L :=
  IsFractionRing.liftAlgHom (evalAt_injective h hx)

/-- The extension to rational functions agrees with evaluation of regular functions. -/
theorem evalFunctionField_algebraMap {x y : L}
    (h : (W.map (algebraMap F L)).Equation x y) (hx : Transcendental F x)
    (f : W.CoordinateRing) :
    evalFunctionField h hx (algebraMap W.CoordinateRing W.FunctionField f) = evalAt h f := by
  exact IsFractionRing.lift_algebraMap (evalAt_injective h hx) f

end WeierstrassCurve.Affine.CoordinateRing

namespace WeierstrassCurve.Affine.FunctionField

open scoped nonZeroDivisors

variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F}

/-- Rational functions generating the same principal fractional ideal differ
by a nonzero ground-field scalar. -/
theorem exists_eq_mul_of_spanSingleton_eq {f g : W.FunctionField}
    (h : FractionalIdeal.spanSingleton W.CoordinateRing⁰ f =
      FractionalIdeal.spanSingleton W.CoordinateRing⁰ g) :
    ∃ c : F, c ≠ 0 ∧ g = algebraMap F W.FunctionField c * f := by
  obtain ⟨u, hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp h
  obtain ⟨c, hc, he⟩ := CoordinateRing.exists_eq_algebraMap_of_isUnit u.isUnit
  refine ⟨c, hc, ?_⟩
  rw [← hu, Units.smul_def, ← he, Algebra.smul_def,
    ← IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField]

/-- A rational function generating the unit fractional ideal is a nonzero constant. -/
theorem exists_eq_algebraMap_of_spanSingleton_eq_one {f : W.FunctionField}
    (h : FractionalIdeal.spanSingleton W.CoordinateRing⁰ f = 1) :
    ∃ c : F, c ≠ 0 ∧ f = algebraMap F W.FunctionField c := by
  have he : FractionalIdeal.spanSingleton W.CoordinateRing⁰ (1 : W.FunctionField) =
      FractionalIdeal.spanSingleton W.CoordinateRing⁰ f := by
    rw [h, FractionalIdeal.spanSingleton_one]
  simpa only [mul_one] using exists_eq_mul_of_spanSingleton_eq he

end WeierstrassCurve.Affine.FunctionField
