/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Constants in the coordinate ring of a Weierstrass curve

The degree formula for the polynomial norm forces every unit in the affine
coordinate ring to be a nonzero constant. In particular, generators of the
same nonzero principal ideal differ by a scalar in the ground field.
-/

@[expose] public section

open Polynomial
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

end WeierstrassCurve.Affine.CoordinateRing
