/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.NTorsionRoots

/-!
# Differential identities for division polynomials

The quadratic differential expression used here is the numerator of the negative
second logarithmic derivative along the invariant vector field. Its product rule
accounts for the extra two-division factor at even indices. All identities in this
file hold over arbitrary commutative rings, so they can be specialized from the
universal Weierstrass curve without restrictions on the characteristic.
-/

@[expose] public section

open Polynomial

namespace WeierstrassCurve

variable {R S : Type*} [CommRing R] [CommRing S] (E : WeierstrassCurve R)

/-- The derivative of the square two-division polynomial is twice the invariant. -/
theorem derivative_Ψ₂Sq : E.Ψ₂Sq.derivative = 2 * E.invar := by
  simp only [Ψ₂Sq, invar, derivative_add, derivative_mul, derivative_pow,
    derivative_X, derivative_C, derivative_ofNat, map_mul, map_ofNat, map_natCast]
  ring

/-- The three-division polynomial measures the logarithmic derivative of `ψ₂`. -/
theorem Ψ₂Sq_mul_derivative_invar_sub :
    E.Ψ₂Sq * E.invar.derivative - E.invar ^ 2 = 4 * E.Ψ₃ := by
  have hb := congrArg (C : R →+* R[X]) E.b_relation
  simp only [map_mul, map_pow, map_sub, map_ofNat] at hb
  simp only [Ψ₂Sq, invar, Ψ₃, derivative_add, derivative_mul, derivative_pow,
    derivative_X, derivative_C, derivative_ofNat, map_mul, map_ofNat, map_natCast]
  linear_combination -hb

/-- The derivative of the three-division polynomial is three times the
square two-division polynomial over any commutative ring. -/
theorem derivative_Ψ₃ : E.Ψ₃.derivative = 3 * E.Ψ₂Sq := by
  simp only [Ψ₃, Ψ₂Sq, derivative_add, derivative_mul, derivative_pow,
    derivative_X, derivative_C, derivative_ofNat, map_mul, map_ofNat, map_natCast]
  ring

/-- The five-division polynomial in terms of the initial division polynomials. -/
theorem preΨ_five : E.preΨ 5 = E.preΨ₄ * E.Ψ₂Sq ^ 2 - E.Ψ₃ ^ 3 := by
  simpa using E.preΨ_odd 2

/-- The first derivative of the auxiliary four-division polynomial. -/
theorem derivative_preΨ₄ :
    E.preΨ₄.derivative = E.invar.derivative * E.Ψ₃ - E.invar * E.Ψ₂Sq := by
  have h := congrArg derivative E.preΨ₄_add_Ψ₂Sq_sq
  simp only [derivative_add, derivative_pow, derivative_mul,
    E.derivative_Ψ₃, E.derivative_Ψ₂Sq, Nat.cast_ofNat, map_ofNat] at h
  linear_combination h

/-- The second derivative of the auxiliary four-division polynomial. -/
theorem derivative_derivative_preΨ₄ : E.preΨ₄.derivative.derivative = 20 * E.Ψ₃ := by
  simp only [preΨ₄, Ψ₃, derivative_add, derivative_mul, derivative_pow,
    derivative_X, derivative_C, derivative_ofNat, derivative_zero, derivative_one,
    derivative_natCast, map_natCast]
  ring

/-- The numerator of the negative second logarithmic derivative of `f` along
 the invariant vector field, after removing the factor `f²`. -/
noncomputable def divisionDifferential (f : R[X]) : R[X] :=
  E.Ψ₂Sq * (f.derivative ^ 2 - f * f.derivative.derivative) -
    E.invar * f * f.derivative

/-- The differential numerator vanishes on the zero polynomial. -/
@[simp] theorem divisionDifferential_zero : E.divisionDifferential 0 = 0 := by
  simp [divisionDifferential]

/-- The differential numerator vanishes on constant polynomials. -/
@[simp] theorem divisionDifferential_C (r : R) : E.divisionDifferential (C r) = 0 := by
  simp [divisionDifferential]

/-- The differential numerator vanishes on one. -/
@[simp] theorem divisionDifferential_one : E.divisionDifferential 1 = 0 := by
  simp [divisionDifferential]

/-- The product rule for the numerator of the second logarithmic derivative. -/
theorem divisionDifferential_mul (f g : R[X]) :
    E.divisionDifferential (f * g) =
      g ^ 2 * E.divisionDifferential f + f ^ 2 * E.divisionDifferential g := by
  simp only [divisionDifferential, derivative_mul, derivative_add]
  ring

/-- The subtraction rule isolates the squared Wronskian needed when applying
the division-polynomial recursions. No polynomial denominators are used. -/
theorem divisionDifferential_sub_mul (f g : R[X]) :
    f * g * E.divisionDifferential (f - g) =
      (f - g) * (g * E.divisionDifferential f - f * E.divisionDifferential g) +
        E.Ψ₂Sq * (g * f.derivative - f * g.derivative) ^ 2 := by
  simp only [divisionDifferential, derivative_sub]
  ring

/-- Squaring doubles the second logarithmic derivative. -/
theorem divisionDifferential_sq (f : R[X]) :
    E.divisionDifferential (f ^ 2) = 2 * f ^ 2 * E.divisionDifferential f := by
  rw [pow_two, E.divisionDifferential_mul]
  ring

/-- The contribution of the square two-division polynomial to the differential numerator. -/
theorem divisionDifferential_Ψ₂Sq :
    E.divisionDifferential E.Ψ₂Sq = -8 * E.Ψ₂Sq * E.Ψ₃ := by
  have hi := E.Ψ₂Sq_mul_derivative_invar_sub
  simp only [divisionDifferential, E.derivative_Ψ₂Sq, derivative_mul,
    derivative_ofNat, zero_mul, zero_add]
  linear_combination -2 * E.Ψ₂Sq * hi

/-- For even indices, the extra `ψ₂` factor contributes `-4 Ψ₃ f²` after
cancelling the common factor in the squared division polynomial. -/
theorem divisionDifferential_sq_mul_Ψ₂Sq (f : R[X]) :
    E.divisionDifferential (f ^ 2 * E.Ψ₂Sq) =
      2 * f ^ 2 * E.Ψ₂Sq *
        (E.Ψ₂Sq * E.divisionDifferential f - 4 * E.Ψ₃ * f ^ 2) := by
  rw [E.divisionDifferential_mul, E.divisionDifferential_sq,
    E.divisionDifferential_Ψ₂Sq]
  ring

/-- The invariant polynomial commutes with change of coefficient ring. -/
theorem map_invar (f : R →+* S) : (E.map f).invar = E.invar.map f := by
  simp [invar, map_b₂, map_b₄]

/-- The differential numerator commutes with change of coefficient ring. -/
theorem map_divisionDifferential (f : R →+* S) (g : R[X]) :
    (E.map f).divisionDifferential (g.map f) = (E.divisionDifferential g).map f := by
  simp only [divisionDifferential, map_Ψ₂Sq, map_invar, derivative_map,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow]

/-- The residual of the division-polynomial differential identity, with the
correction for the extra `ψ₂` factor at even indices. Vanishing at an odd index
is exactly the unsquared differential identity. -/
noncomputable def divisionDifferentialDefect (n : ℤ) : R[X] :=
  (if Even n then
    E.Ψ₂Sq * E.divisionDifferential (E.preΨ n) - 4 * E.Ψ₃ * E.preΨ n ^ 2
  else E.divisionDifferential (E.preΨ n)) -
    C ((n : R) ^ 2) * (E.Φ n - X * E.ΨSq n)

/-- The differential identity has the same form for every squared division
polynomial, after multiplication by the indicated common factor. -/
theorem divisionDifferential_ΨSq (n : ℤ) :
    E.divisionDifferential (E.ΨSq n) -
        2 * C ((n : R) ^ 2) * (E.Φ n - X * E.ΨSq n) * E.ΨSq n =
      2 * E.ΨSq n * E.divisionDifferentialDefect n := by
  unfold divisionDifferentialDefect ΨSq
  split_ifs with hn
  · rw [E.divisionDifferential_sq_mul_Ψ₂Sq]
    ring
  · simp only [mul_one, E.divisionDifferential_sq]
    ring

/-- The differential identity holds at index zero over every commutative ring. -/
@[simp] theorem divisionDifferentialDefect_zero : E.divisionDifferentialDefect 0 = 0 := by
  simp [divisionDifferentialDefect]

/-- The differential identity holds at index one over every commutative ring. -/
@[simp] theorem divisionDifferentialDefect_one : E.divisionDifferentialDefect 1 = 0 := by
  simp [divisionDifferentialDefect]

/-- The corrected even identity holds at index two over every commutative ring. -/
@[simp] theorem divisionDifferentialDefect_two : E.divisionDifferentialDefect 2 = 0 := by
  simp [divisionDifferentialDefect, WeierstrassCurve.Φ, map_ofNat]
  ring

/-- The odd differential identity holds at index three over every commutative ring. -/
@[simp] theorem divisionDifferentialDefect_three : E.divisionDifferentialDefect 3 = 0 := by
  have hf := E.preΨ₄_add_Ψ₂Sq_sq
  simp only [divisionDifferentialDefect, show ¬Even (3 : ℤ) by decide, ite_false,
    preΨ_three, Φ_three, ΨSq_three, divisionDifferential, E.derivative_Ψ₃,
    derivative_mul, derivative_ofNat, zero_mul, zero_add, E.derivative_Ψ₂Sq]
  norm_num only [Int.cast_ofNat, Nat.cast_ofNat, map_pow, map_ofNat]
  linear_combination 9 * E.Ψ₂Sq * hf

/-- The corrected even identity holds at index four over every commutative ring. -/
@[simp] theorem divisionDifferentialDefect_four : E.divisionDifferentialDefect 4 = 0 := by
  have hi := E.Ψ₂Sq_mul_derivative_invar_sub
  have hf : E.preΨ₄ = E.invar * E.Ψ₃ - E.Ψ₂Sq ^ 2 :=
    eq_sub_iff_add_eq.mpr E.preΨ₄_add_Ψ₂Sq_sq
  simp only [divisionDifferentialDefect, show Even (4 : ℤ) by decide, ite_true,
    preΨ_four, WeierstrassCurve.Φ, ΨSq_four]
  norm_num only [Int.reduceAdd, Int.reduceSub, preΨ_three, E.preΨ_five,
    Int.cast_ofNat, Nat.cast_ofNat, map_pow, map_ofNat]
  rw [divisionDifferential, E.derivative_derivative_preΨ₄, E.derivative_preΨ₄, hf]
  linear_combination (E.Ψ₂Sq * E.Ψ₃ *
    (E.invar.derivative * E.Ψ₃ - E.invar * E.Ψ₂Sq) + 4 * E.Ψ₃ ^ 3) * hi

/-- The differential residual commutes with change of coefficient ring. -/
theorem map_divisionDifferentialDefect (f : R →+* S) (n : ℤ) :
    (E.map f).divisionDifferentialDefect n = (E.divisionDifferentialDefect n).map f := by
  unfold divisionDifferentialDefect
  split_ifs <;>
    simp only [map_Ψ₂Sq, map_Ψ₃, map_preΨ, map_Φ, map_ΨSq, map_divisionDifferential,
      Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_ofNat,
      Polynomial.map_X, map_pow, map_intCast, Polynomial.map_intCast]

/-- A universal differential identity specializes to every Weierstrass curve,
including curves in characteristics two and three. -/
theorem divisionDifferentialDefect_eq_zero_of_universal {n : ℤ}
    (h : Universal.curve.divisionDifferentialDefect n = 0) :
    E.divisionDifferentialDefect n = 0 := by
  rw [← E.map_specialize, map_divisionDifferentialDefect, h, Polynomial.map_zero]

end WeierstrassCurve
