/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Constants and evaluation in a Weierstrass coordinate ring

The degree formula for the polynomial norm forces every unit in the affine
coordinate ring to be a nonzero constant. In particular, generators of the
same principal ideal differ by a scalar in the ground field. Evaluation has
the point ideal as its kernel and commutes with homomorphisms of ground fields.
Fixing a generator's value to one at a point makes it unique.
-/

@[expose] public section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine.CoordinateRing

variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F}

/-- Every unit of the affine coordinate ring is a nonzero constant. -/
theorem exists_eq_algebraMap_of_isUnit {f : W.CoordinateRing} (hf : IsUnit f) :
    ∃ c : F, c ≠ 0 ∧ algebraMap F W.CoordinateRing c = f := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq f
  have hd := Polynomial.degree_eq_zero_of_isUnit (hf.map (Algebra.norm F[X]))
  rw [degree_norm_smul_basis] at hd
  have hq : q = 0 := by
    by_contra hq
    have hqd := Polynomial.degree_eq_natDegree hq
    have hh := (le_max_right (2 • p.degree) (2 • q.degree + 3)).trans hd.le
    rw [hqd] at hh
    norm_cast at hh
  subst q
  simp only [zero_smul, add_zero] at hd ⊢ hf
  have hp : p.degree ≤ 0 := by
    have hh := (le_max_left (2 • p.degree) (2 • (0 : F[X]).degree + 3)).trans hd.le
    by_cases hp0 : p = 0
    · simp [hp0]
    · rw [Polynomial.degree_eq_natDegree hp0] at hh ⊢
      rw [two_nsmul] at hh
      have hh' : p.natDegree + p.natDegree ≤ 0 := by exact_mod_cast hh
      exact_mod_cast (show p.natDegree ≤ 0 by omega)
  refine ⟨p.coeff 0, ?_, ?_⟩
  · intro hc
    rw [Polynomial.eq_C_of_degree_le_zero hp, hc, C_0, zero_smul] at hf
    exact not_isUnit_zero hf
  · rw [Polynomial.eq_C_of_degree_le_zero hp]
    simp [Algebra.smul_def, IsScalarTower.algebraMap_apply F F[X] W.CoordinateRing]

/-- Generators of the same principal ideal differ by a nonzero ground-field scalar. -/
theorem exists_eq_smul_of_span_eq {f g : W.CoordinateRing}
    (h : Ideal.span {f} = Ideal.span {g}) :
    ∃ c : F, c ≠ 0 ∧ g = c • f := by
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp h
  obtain ⟨c, hc, he⟩ := exists_eq_algebraMap_of_isUnit u.isUnit
  refine ⟨c, hc, ?_⟩
  rw [← hu, ← he, Algebra.smul_def, mul_comm]

/-- Evaluation at an affine point vanishes exactly on its point ideal. -/
theorem evalEval_eq_zero_iff {x y : F} (h : W.Equation x y) (f : W.CoordinateRing) :
    AdjoinRoot.evalEval h f = 0 ↔ f ∈ XYIdeal W x (C y) := by
  change W.polynomial.evalEval x y = 0 at h
  have hm : XYIdeal W x (C y) =
      Ideal.map (mk W) (Ideal.span {C (X - C x), Y - C (C y)}) := by
    simp only [XYIdeal, XClass, YClass, Ideal.map_span, Set.image_pair]
  rw [hm, Ideal.mem_map_iff_of_surjective (mk W) (AdjoinRoot.mk_surjective)]
  constructor
  · intro hf
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective f
    rw [AdjoinRoot.evalEval_mk] at hf
    exact ⟨p, mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mpr hf, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    change AdjoinRoot.evalEval h (AdjoinRoot.mk _ p) = 0
    rw [AdjoinRoot.evalEval_mk]
    exact mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mp hp

/-- Inclusion of affine point ideals forces equality of both coordinates. -/
theorem XYIdeal_le_XYIdeal_iff {x y x' y' : F} (h : W.Equation x' y') :
    XYIdeal W x (C y) ≤ XYIdeal W x' (C y') ↔ x = x' ∧ y = y' := by
  constructor
  · intro hle
    have hx : AdjoinRoot.evalEval h (XClass W x) = 0 :=
      (evalEval_eq_zero_iff h _).mpr (hle (Ideal.subset_span (by simp)))
    have hy : AdjoinRoot.evalEval h (YClass W (C y)) = 0 :=
      (evalEval_eq_zero_iff h _).mpr (hle (Ideal.subset_span (by simp)))
    change W.polynomial.evalEval x' y' = 0 at h
    simp only [XClass, YClass, AdjoinRoot.evalEval_mk, evalEval, eval_C, eval_sub,
      eval_X] at hx hy
    exact ⟨(sub_eq_zero.mp hx).symm, (sub_eq_zero.mp hy).symm⟩
  · rintro ⟨rfl, rfl⟩
    exact le_rfl

/-- Extending scalars sends a point ideal to the ideal of the mapped point. -/
theorem map_XYIdeal {L : Type*} [Field L] (φ : F →+* L) (x y : F) :
    Ideal.map (map W φ) (XYIdeal W x (C y)) =
      XYIdeal (W.map φ) (φ x) (C (φ y)) := by
  simp only [XYIdeal, Ideal.map_span, Set.image_pair, XClass, YClass, map_mk,
    Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X, Polynomial.coe_mapRingHom]

/-- Evaluation commutes with applying a homomorphism of ground fields. -/
theorem evalEval_map {L : Type*} [Field L] {x y : F} (h : W.Equation x y)
    (φ : F →+* L) (f : W.CoordinateRing) :
    AdjoinRoot.evalEval ((W.map_equation φ.injective x y).mpr h) (map W φ f) =
      φ (AdjoinRoot.evalEval h f) := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective f
  have h₀ : W.polynomial.evalEval x y = 0 := h
  have h₁ : (W.map φ).polynomial.evalEval (φ x) (φ y) = 0 :=
    (W.map_equation φ.injective x y).mpr h
  change AdjoinRoot.evalEval h₁ (map W φ (AdjoinRoot.mk _ p)) =
    φ (AdjoinRoot.evalEval h₀ (AdjoinRoot.mk _ p))
  rw [map_mk]
  change AdjoinRoot.evalEval _ (AdjoinRoot.mk _ _) = _
  rw [AdjoinRoot.evalEval_mk, AdjoinRoot.evalEval_mk]
  exact map_mapRingHom_evalEval φ p x y

/-- Evaluation fixes constants from the ground field. -/
theorem evalEval_algebraMap {x y : F} (h : W.Equation x y) (c : F) :
    AdjoinRoot.evalEval h (algebraMap F W.CoordinateRing c) = c := by
  have h₀ : W.polynomial.evalEval x y = 0 := h
  change AdjoinRoot.evalEval h₀ (AdjoinRoot.mk _ (C (C c))) = c
  rw [AdjoinRoot.evalEval_mk]
  simp

/-- Evaluation is linear over the ground field. -/
theorem evalEval_smul {x y : F} (h : W.Equation x y) (c : F)
    (f : W.CoordinateRing) :
    AdjoinRoot.evalEval h (c • f) = c * AdjoinRoot.evalEval h f := by
  rw [Algebra.smul_def, map_mul, evalEval_algebraMap]

/-- Two generators of the same ideal that both evaluate to one at a point are equal. -/
theorem eq_of_span_eq_of_evalEval_eq_one {f g : W.CoordinateRing}
    (hfg : Ideal.span {f} = Ideal.span {g})
    {x y : F} (h : W.Equation x y) (hf : AdjoinRoot.evalEval h f = 1)
    (hg : AdjoinRoot.evalEval h g = 1) : f = g := by
  obtain ⟨c, _, rfl⟩ := exists_eq_smul_of_span_eq hfg
  rw [evalEval_smul, hf, mul_one] at hg
  rw [hg, one_smul]

end WeierstrassCurve.Affine.CoordinateRing
