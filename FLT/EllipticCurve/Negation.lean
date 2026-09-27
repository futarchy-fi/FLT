/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CoordinateRing

/-!
# Negation on the affine coordinate ring

Pullback by point negation is the conjugation of the quadratic algebra over
`F[X]`. It sends the ideal of a point to that of its negative, and multiplying
a function by its conjugate gives its polynomial norm.
-/

@[expose] public section

open Polynomial
open scoped Polynomial.Bivariate
namespace WeierstrassCurve.Affine.CoordinateRing
variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)
/-- Pullback by point negation, fixing the polynomial subring in the x-coordinate. -/
noncomputable def negHom : W.CoordinateRing →ₐ[F[X]] W.CoordinateRing :=
  AdjoinRoot.liftAlgHom W.polynomial (Algebra.ofId _ _) (mk W W.negPolynomial) (by
    change eval₂ (algebraMap F[X] W.CoordinateRing) (mk W W.negPolynomial) W.polynomial = 0
    change aeval (mk W W.negPolynomial) W.polynomial = 0
    rw [← AdjoinRoot.aeval_eq, ← Polynomial.aeval_comp]
    have h : W.polynomial.comp W.negPolynomial = W.polynomial := by
      simp only [WeierstrassCurve.Affine.polynomial, WeierstrassCurve.Affine.negPolynomial,
        Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.pow_comp,
        Polynomial.X_comp, Polynomial.C_comp]
      ring
    rw [h, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])
/-- Negation substitutes the negation polynomial in any representative. -/
theorem negHom_mk (p : F[X][Y]) : negHom W (mk W p) = mk W (p.comp W.negPolynomial) := by
  rw [negHom, AdjoinRoot.liftAlgHom_mk]
  change aeval (mk W W.negPolynomial) p = _
  rw [← AdjoinRoot.aeval_eq, ← Polynomial.aeval_comp, AdjoinRoot.aeval_eq]

/-- Negation fixes the vertical-line function. -/
theorem negHom_XClass (x : F) : negHom W (XClass W x) = XClass W x := by
  rw [XClass, negHom_mk, Polynomial.C_comp]

/-- Negation of a horizontal-line function, modulo its vertical-line correction. -/
theorem negHom_YClass (x y : F) :
    negHom W (YClass W (C y)) = -YClass W (C (W.negY x y)) +
      XClass W x * mk W (C (C (-W.a₁))) := by
  simp only [YClass, XClass, negHom_mk, Polynomial.sub_comp, Polynomial.X_comp,
    Polynomial.C_comp, ← map_neg, ← map_mul, ← map_add]
  congr 1
  simp only [WeierstrassCurve.Affine.negPolynomial, WeierstrassCurve.Affine.negY]
  simp only [map_add, map_mul, map_sub, map_neg]
  ring

/-- Negation sends a point ideal to the ideal of the negative point. -/
theorem map_negHom_XYIdeal (x y : F) :
    Ideal.map (negHom W).toRingHom (XYIdeal W x (C y)) =
      XYIdeal W x (C (W.negY x y)) := by
  simp only [XYIdeal, Ideal.map_span, Set.image_pair]
  change Ideal.span {negHom W (XClass W x), negHom W (YClass W (C y))} = _
  rw [negHom_XClass, negHom_YClass W x y, Ideal.span_pair_add_left_mul, Ideal.span_pair_neg]

/-- Pullback by negation is an involution. -/
theorem negHom_negHom (f : W.CoordinateRing) : negHom W (negHom W f) = f := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq f
  have hY : negHom W (mk W Y) = -mk W Y - algebraMap F[X] W.CoordinateRing
      (C W.a₁ * X + C W.a₃) := by
    rw [negHom_mk, Polynomial.X_comp, WeierstrassCurve.Affine.negPolynomial,
      map_sub, map_neg]
    rfl
  simp only [map_add, map_smul, map_one, hY, map_sub, map_neg, AlgHom.commutes]
  module

/-- Multiplying a function by its negation pullback gives its polynomial norm. -/
theorem mul_negHom (f : W.CoordinateRing) :
    f * negHom W f = algebraMap F[X] W.CoordinateRing (Algebra.norm F[X] f) := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq f
  rw [AdjoinRoot.algebraMap_eq, coe_norm_smul_basis]
  simp only [map_mul, map_add, map_smul, map_one, negHom_mk, Polynomial.X_comp,
    WeierstrassCurve.Affine.negPolynomial]
  simp only [Algebra.smul_def, mul_one]
  rfl

end WeierstrassCurve.Affine.CoordinateRing
