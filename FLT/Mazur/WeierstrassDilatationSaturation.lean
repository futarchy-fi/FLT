/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationAlgebra

/-!
# Saturation on the divided chart

The original cubic under x=s*u, y=s*v is exactly s² times the divided
polynomial. Flatness makes the scale regular in the actual divided algebra,
so saturation of the original relation recovers its defining ideal.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.WeierstrassDilatation

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The original cubic with both original coordinates scaled by s. -/
def originalTransformPolynomial : R[X][X] :=
  (C (C s) * X) ^ 2 + C (C W.a₁ * (C s * X)) * (C (C s) * X) +
    C (C W.a₃) * (C (C s) * X) -
      C ((C s * X) ^ 3 + C W.a₂ * (C s * X) ^ 2 + C W.a₄ * (C s * X) + C W.a₆)

/-- The exact common factor in the original transformed cubic. -/
theorem originalTransform_identity (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4)
    (h6 : W.a₆ = s ^ 2 * b6) :
    originalTransformPolynomial W s = C (C s) ^ 2 * polynomial W s b3 b4 b6 := by
  simp only [originalTransformPolynomial, polynomial, h3, h4, h6,
    map_add, map_mul, map_pow]
  ring

/-- The polynomial quotient carries its scale to the original base scale. -/
theorem mk_scale : AdjoinRoot.mk (polynomial W s b3 b4 b6) (C (C s)) =
    algebraMap R (Coordinate W s b3 b4 b6) s := by
  exact (IsScalarTower.algebraMap_apply R R[X] _ s).symm

/-- Powers of the scale cannot create new relations in the actual divided chart. -/
theorem scale_pow_mul_mem_iff (hs : IsRegular s) (n : ℕ) (p : R[X][X]) :
    C (C s) ^ n * p ∈ Ideal.span {polynomial W s b3 b4 b6} ↔
      p ∈ Ideal.span {polynomial W s b3 b4 b6} := by
  constructor
  · intro h
    apply Ideal.mem_span_singleton.mpr
    apply AdjoinRoot.mk_eq_zero.mp
    have hz := AdjoinRoot.mk_eq_zero.mpr (Ideal.mem_span_singleton.mp h)
    rw [map_mul, map_pow, mk_scale] at hz
    exact ((scale_regular W s b3 b4 b6 hs).pow n).left
      (hz.trans (mul_zero _).symm)
  · exact fun h => Ideal.mul_mem_left _ _ h

/-- Saturating the original equation gives precisely the actual divided relation. -/
theorem originalTransform_saturation (hs : IsRegular s)
    (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
    (p : R[X][X]) :
    (∃ n : ℕ, C (C s) ^ n * p ∈ Ideal.span {originalTransformPolynomial W s}) ↔
      p ∈ Ideal.span {polynomial W s b3 b4 b6} := by
  rw [originalTransform_identity W s b3 b4 b6 h3 h4 h6]
  constructor
  · rintro ⟨n, hn⟩
    apply (scale_pow_mul_mem_iff W s b3 b4 b6 hs n p).mp
    exact Ideal.mem_span_singleton.mpr
      (dvd_trans (dvd_mul_left _ _) (Ideal.mem_span_singleton.mp hn))
  · intro hp
    refine ⟨2, Ideal.mem_span_singleton.mpr ?_⟩
    exact mul_dvd_mul_left _ (Ideal.mem_span_singleton.mp hp)

/-- The actual quotient map detects exactly the saturated original cubic. -/
theorem originalTransform_saturation_iff_mk (hs : IsRegular s)
    (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
    (p : R[X][X]) :
    (∃ n : ℕ, C (C s) ^ n * p ∈ Ideal.span {originalTransformPolynomial W s}) ↔
      AdjoinRoot.mk (polynomial W s b3 b4 b6) p = 0 := by
  rw [originalTransform_saturation W s b3 b4 b6 hs h3 h4 h6,
    Ideal.mem_span_singleton, AdjoinRoot.mk_eq_zero]

end FLT.Mazur.WeierstrassDilatation
