/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CoordinateRing
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import FLT.Mathlib.RingTheory.DedekindDomain.Invertible
/-!
# The elliptic coordinate ring is Dedekind

Over an algebraically closed field, every maximal ideal is an affine point
ideal. On an elliptic curve these point ideals are invertible. The Noetherian
criterion therefore makes the coordinate ring a Dedekind domain.
-/

@[expose] public section

open Polynomial
open scoped Polynomial.Bivariate nonZeroDivisors
namespace WeierstrassCurve.Affine.CoordinateRing
variable {F : Type*} [Field F] [IsAlgClosed F] {W : WeierstrassCurve.Affine F}
/-- Every maximal ideal of a Weierstrass coordinate ring over an algebraically
closed field is the ideal of an affine rational point. -/
theorem exists_eq_XYIdeal_of_isMaximal (I : Ideal W.CoordinateRing) [I.IsMaximal] :
    ∃ x y : F, W.Equation x y ∧ I = XYIdeal W x (C y) := by
  let : Field (W.CoordinateRing ⧸ I) := Ideal.Quotient.field I
  let : Module.Finite F (W.CoordinateRing ⧸ I) :=
    finite_of_finite_type_of_isJacobsonRing F (W.CoordinateRing ⧸ I)
  let φ : W.CoordinateRing →ₐ[F] F :=
    IsAlgClosed.lift.comp (Ideal.Quotient.mkₐ F I)
  let x : F := φ (mk W (C X))
  let y : F := φ (mk W Y)
  have hC (a : F) : φ (mk W (C (C a))) = a := φ.commutes a
  have he : W.Equation x y := by
    have h : φ (mk W (Y ^ 2 + C (C W.a₁ * X + C W.a₃) * Y -
        C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆))) = 0 :=
      (congrArg φ (AdjoinRoot.mk_self (f := W.polynomial))).trans (map_zero φ)
    rw [equation_iff']
    simpa only [map_sub, map_add, map_mul, map_pow, hC, add_mul, x, y, add_assoc] using h
  have hker (a : W.CoordinateRing) : φ a = 0 ↔ a ∈ I := by
    change IsAlgClosed.lift (Ideal.Quotient.mk I a) = 0 ↔ a ∈ I
    rw [map_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨x, y, he, ((isMaximal_XYIdeal he).eq_of_le
    (Ideal.IsMaximal.ne_top inferInstance) ?_).symm⟩
  rw [XYIdeal, Ideal.span_le, Set.pair_subset_iff]
  constructor
  · apply (hker _).mp
    simp only [XClass, map_sub, hC, x, sub_self]
  · apply (hker _).mp
    simp only [YClass, map_sub, hC, y, sub_self]
variable [W.IsElliptic]
/-- The affine coordinate ring of an elliptic curve over an algebraically
closed field is a Dedekind domain. -/
instance instIsDedekindDomain : IsDedekindDomain W.CoordinateRing := by
  classical
  apply isDedekindDomain_of_isUnit_maximals (K := W.FunctionField)
  intro M hM
  have := hM
  obtain ⟨x, y, he, rfl⟩ := exists_eq_XYIdeal_of_isMaximal M
  rw [← XYIdeal'_eq (W.equation_iff_nonsingular.mp he)]
  exact (XYIdeal' (W.equation_iff_nonsingular.mp he)).isUnit
end WeierstrassCurve.Affine.CoordinateRing
