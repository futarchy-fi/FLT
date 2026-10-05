/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# A divisibility obstruction to singular reduction

If x,y,a₃,a₄ belong to an ideal I, the Weierstrass equation forces a₆ into I².
For a normalized singular point at the origin, this is the elementary
point-exclusion step of Tate's type II case. It does not assert that an
arbitrary minimal equation has this normal form, or classify its other cases.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (I : Ideal R)

/-- Integral points above the origin force second-order divisibility of a₆. -/
theorem a₆_mem_ideal_sq_of_equation {x y : R} (h : W.toAffine.Equation x y)
    (hx : x ∈ I) (hy : y ∈ I) (h₃ : W.a₃ ∈ I) (h₄ : W.a₄ ∈ I) :
    W.a₆ ∈ I ^ 2 := by
  have hxy : x * y ∈ I ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul hx hy
  have h3y : W.a₃ * y ∈ I ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul h₃ hy
  have h4x : W.a₄ * x ∈ I ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul h₄ hx
  have hx2 : x ^ 2 ∈ I ^ 2 := Ideal.pow_mem_pow hx 2
  have hy2 : y ^ 2 ∈ I ^ 2 := Ideal.pow_mem_pow hy 2
  have he : W.a₆ = y ^ 2 + W.a₁ * (x * y) + W.a₃ * y -
      (x * x ^ 2 + W.a₂ * x ^ 2 + W.a₄ * x) := by
    have hh := (Affine.equation_iff _ _).mp h
    linear_combination -hh
  rw [he]
  exact (I ^ 2).sub_mem
    ((I ^ 2).add_mem ((I ^ 2).add_mem hy2 ((I ^ 2).mul_mem_left _ hxy)) h3y)
    ((I ^ 2).add_mem ((I ^ 2).add_mem ((I ^ 2).mul_mem_left _ hx2)
      ((I ^ 2).mul_mem_left _ hx2)) h4x)

/-- If a₆ has order one, no integral point can have both coordinates in I. -/
theorem not_mem_ideal_pair_of_a₆_not_mem_sq {x y : R} (h : W.toAffine.Equation x y)
    (h₃ : W.a₃ ∈ I) (h₄ : W.a₄ ∈ I) (h₆ : W.a₆ ∉ I ^ 2) :
    ¬ (x ∈ I ∧ y ∈ I) :=
  fun hxy => h₆ (a₆_mem_ideal_sq_of_equation W I h hxy.1 hxy.2 h₃ h₄)

/-- The local-ring version excludes reduction to the affine origin. -/
theorem residue_pair_ne_zero_of_a₆_not_mem_sq [IsLocalRing R] {x y : R}
    (h : W.toAffine.Equation x y)
    (h₃ : W.a₃ ∈ IsLocalRing.maximalIdeal R) (h₄ : W.a₄ ∈ IsLocalRing.maximalIdeal R)
    (h₆ : W.a₆ ∉ IsLocalRing.maximalIdeal R ^ 2) :
    ¬ (IsLocalRing.residue R x = 0 ∧ IsLocalRing.residue R y = 0) := by
  simpa only [IsLocalRing.residue_eq_zero_iff] using
    not_mem_ideal_pair_of_a₆_not_mem_sq W (IsLocalRing.maximalIdeal R) h h₃ h₄ h₆

end FLT.Mazur
