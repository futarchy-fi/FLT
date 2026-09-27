/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.KnownIn1980s.EllipticCurves.TateCurveBaseChange
public import FLT.KnownIn1980s.EllipticCurves.TateCurveConstruction
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Integral specialization of the formal Tate coordinates

The coordinate coefficients lie in `ℤ[u, u⁻¹, (1-u)⁻¹]`. Working in this
localization allows the formal Weierstrass identity to specialize in every
characteristic, including characteristics two and three.
-/

@[expose] public section

open scoped PowerSeries ArithmeticFunction.sigma

namespace TateCurve

noncomputable section

/-- The formal `x`-coordinate with the two required inverses supplied explicitly. -/
def integralX {R : Type*} [CommRing R] (u ui vi : R) : R⟦X⟧ :=
  .C (u * vi ^ 2) + .mk fun n ↦ ∑ d ∈ n.divisors, d * (u ^ d + ui ^ d - 2)

/-- The formal `y`-coordinate with the two required inverses supplied explicitly. -/
def integralY {R : Type*} [CommRing R] (u ui vi : R) : R⟦X⟧ :=
  .C (u ^ 2 * vi ^ 3) + .mk fun n ↦ ∑ d ∈ n.divisors,
    (d.choose 2 * u ^ d - (d + 1).choose 2 * ui ^ d + d)

/-- The integral `x`-series commutes with coefficient homomorphisms. -/
theorem map_integralX {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u ui vi : R) :
    PowerSeries.map f (integralX u ui vi) = integralX (f u) (f ui) (f vi) := by
  ext n
  simp [integralX, map_ofNat]

/-- The integral `y`-series commutes with coefficient homomorphisms. -/
theorem map_integralY {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u ui vi : R) :
    PowerSeries.map f (integralY u ui vi) = integralY (f u) (f ui) (f vi) := by
  ext n
  simp [integralY]

/-- The numerator defining each `a₆` coefficient is divisible by twelve over the integers. -/
theorem twelve_dvd_sigma (n : ℕ) : (12 : ℤ) ∣ 5 * (σ 3 n : ℤ) + 7 * (σ 5 n : ℤ) := by
  have hd (d : ℤ) : (12 : ℤ) ∣ 5 * d ^ 3 + 7 * d ^ 5 := by
    have hz : ((5 * d ^ 3 + 7 * d ^ 5 : ℤ) : ZMod 12) = 0 := by
      push_cast
      generalize (d : ZMod 12) = r
      revert r
      decide
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12).mp hz
  have hs : 5 * (σ 3 n : ℤ) + 7 * (σ 5 n : ℤ) =
      ∑ d ∈ n.divisors, (5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5) := by
    simp only [ArithmeticFunction.sigma_apply, Nat.cast_sum, Nat.cast_pow,
      Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hs]
  exact Finset.dvd_sum fun d _ ↦ hd d

/-- The integral `s`-series maps to the rational-function coefficient series. -/
theorem map_sInt (k : ℕ) : PowerSeries.map (Int.castRingHom (RatFunc ℚ)) (sInt k) = s k := by
  ext n
  simp [sInt, s]

/-- The integral `a₄` maps to the coefficient in the rational-function identity. -/
theorem map_a₄Formal : PowerSeries.map (Int.castRingHom (RatFunc ℚ)) a₄Formal = a₄ := by
  simp [a₄Formal, a₄, map_sInt, map_ofNat]

/-- Exact integer division identifies `a₆` with its characteristic-zero formula. -/
theorem map_a₆Formal : PowerSeries.map (Int.castRingHom (RatFunc ℚ)) a₆Formal = a₆ := by
  ext n
  have h := congrArg (fun z : ℤ ↦ (z : RatFunc ℚ)) (Int.ediv_mul_cancel (twelve_dvd_sigma n))
  push_cast at h
  simp only [PowerSeries.coeff_map, coeff_a₆Formal]
  simp only [a₆, s, PowerSeries.coeff_smul, map_neg, map_add,
    show (5 : (RatFunc ℚ)⟦X⟧) = PowerSeries.C 5 from (map_ofNat PowerSeries.C 5).symm,
    show (7 : (RatFunc ℚ)⟦X⟧) = PowerSeries.C 7 from (map_ofNat PowerSeries.C 7).symm,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, smul_eq_mul]
  linear_combination -h / 12


/-- The polynomial whose inversion removes exactly the coordinate poles at zero and one. -/
def coordinateDenominator : Polynomial ℤ := Polynomial.X * (1 - Polynomial.X)

/-- The integral coefficient ring `ℤ[u, u⁻¹, (1-u)⁻¹]` of the Tate coordinates. -/
abbrev CoordinateRing := Localization.Away coordinateDenominator

/-- The universal coordinate parameter in the integral coefficient ring. -/
def coordinateU : CoordinateRing := algebraMap (Polynomial ℤ) CoordinateRing Polynomial.X

/-- The inverse of the universal parameter. -/
def coordinateUInv : CoordinateRing :=
  (1 - coordinateU) * IsLocalization.Away.invSelf coordinateDenominator

/-- The inverse of one minus the universal parameter. -/
def coordinateOneSubInv : CoordinateRing :=
  coordinateU * IsLocalization.Away.invSelf coordinateDenominator

/-- The explicit universal inverse of `u` is a right inverse. -/
theorem coordinateU_mul_inv : coordinateU * coordinateUInv = 1 := by
  simpa [coordinateDenominator, coordinateU, coordinateUInv, map_mul, map_sub, mul_assoc]
    using (IsLocalization.Away.mul_invSelf (S := CoordinateRing) coordinateDenominator)

/-- The explicit universal inverse of `1-u` is a right inverse. -/
theorem coordinateOneSub_mul_inv : (1 - coordinateU) * coordinateOneSubInv = 1 := by
  simpa only [coordinateUInv, coordinateOneSubInv, mul_left_comm] using coordinateU_mul_inv

/-- Specialize the integral coefficient ring at any field element other than zero and one. -/
def coordinateEval {K : Type*} [Field K] (u : K) (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    CoordinateRing →+* K :=
  IsLocalization.Away.lift coordinateDenominator
    (g := Polynomial.eval₂RingHom (Int.castRingHom K) u)
    (by simpa [coordinateDenominator] using
      (isUnit_iff_ne_zero.mpr (mul_ne_zero hu0 (sub_ne_zero.mpr hu1.symm))))

/-- Specialization sends the universal parameter to the supplied element. -/
@[simp]
theorem coordinateEval_u {K : Type*} [Field K] (u : K) (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    coordinateEval u hu0 hu1 coordinateU = u := by
  simp [coordinateEval, coordinateU, IsLocalization.Away.lift_eq]

/-- Specialization respects the inverse of the universal parameter. -/
@[simp]
theorem coordinateEval_uInv {K : Type*} [Field K] (u : K) (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    coordinateEval u hu0 hu1 coordinateUInv = u⁻¹ := by
  apply mul_left_cancel₀ hu0
  rw [mul_inv_cancel₀ hu0]
  simpa using congrArg (coordinateEval u hu0 hu1) coordinateU_mul_inv

/-- Specialization respects the inverse of one minus the universal parameter. -/
@[simp]
theorem coordinateEval_oneSubInv {K : Type*} [Field K] (u : K) (hu0 : u ≠ 0)
    (hu1 : u ≠ 1) : coordinateEval u hu0 hu1 coordinateOneSubInv = (1 - u)⁻¹ := by
  apply mul_left_cancel₀ (sub_ne_zero.mpr hu1.symm)
  rw [mul_inv_cancel₀ (sub_ne_zero.mpr hu1.symm)]
  simpa using congrArg (coordinateEval u hu0 hu1) coordinateOneSub_mul_inv

/-- Polynomial evaluation at the rational-function variable is injective over the integers. -/
private theorem polynomial_eval_ratFunc_injective : Function.Injective
    (Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) (RatFunc.X : RatFunc ℚ)) := by
  have heq : Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X =
      (algebraMap (Polynomial ℚ) (RatFunc ℚ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℚ)) := by
    ext <;> simp
  rw [heq]
  exact (RatFunc.algebraMap_injective ℚ).comp
    (Polynomial.map_injective _ Int.cast_injective)

/-- The universal parameter is distinct from one in the rational-function field. -/
theorem ratFunc_X_ne_one : (RatFunc.X : RatFunc ℚ) ≠ 1 := by
  intro h
  have h' : Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X
      (Polynomial.X : Polynomial ℤ) =
      Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X 1 := by simpa using h
  have := polynomial_eval_ratFunc_injective h'
  exact Polynomial.X_ne_C (1 : ℤ) (by simpa using this)

/-- The integral coefficient ring embeds into the rational-function field used by the
complex proof of the Tate equation. -/
theorem coordinateEval_ratFunc_injective : Function.Injective
    (coordinateEval (RatFunc.X : RatFunc ℚ) RatFunc.X_ne_zero ratFunc_X_ne_one) := by
  apply IsLocalization.injective_of_map_algebraMap_zero
    (M := Submonoid.powers coordinateDenominator)
  intro p hp
  have he : Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X p = 0 := by
    simpa [coordinateEval, IsLocalization.Away.lift_eq] using hp
  have hp0 : p = 0 := polynomial_eval_ratFunc_injective (by simpa using he)
  simp [hp0]


/-- Mapping an integral scalar series twice is the same as casting its coefficients. -/
theorem map_map_intCast {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (F : ℤ⟦X⟧) : PowerSeries.map f (PowerSeries.map (Int.castRingHom R) F) =
      PowerSeries.map (Int.castRingHom S) F := by
  ext n
  simp

/-- The formal Tate equation already holds over the integral coefficient ring.
The proof descends along its injection into `ℚ(u)`, so it does not invert twelve. -/
theorem integral_weierstrass_equation :
    integralY coordinateU coordinateUInv coordinateOneSubInv ^ 2 +
        integralX coordinateU coordinateUInv coordinateOneSubInv *
          integralY coordinateU coordinateUInv coordinateOneSubInv =
      integralX coordinateU coordinateUInv coordinateOneSubInv ^ 3 +
        PowerSeries.map (Int.castRingHom CoordinateRing) a₄Formal *
          integralX coordinateU coordinateUInv coordinateOneSubInv +
        PowerSeries.map (Int.castRingHom CoordinateRing) a₆Formal := by
  let f := coordinateEval (RatFunc.X : RatFunc ℚ) RatFunc.X_ne_zero ratFunc_X_ne_one
  apply PowerSeries.map_injective f coordinateEval_ratFunc_injective
  have hx : PowerSeries.map f (integralX coordinateU coordinateUInv coordinateOneSubInv) = X := by
    rw [map_integralX]
    simp only [f, coordinateEval_u, coordinateEval_uInv, coordinateEval_oneSubInv]
    simp only [integralX, X, div_eq_mul_inv, inv_pow]
  have hy : PowerSeries.map f (integralY coordinateU coordinateUInv coordinateOneSubInv) = Y := by
    rw [map_integralY]
    simp only [f, coordinateEval_u, coordinateEval_uInv, coordinateEval_oneSubInv]
    simp only [integralY, Y, div_eq_mul_inv, inv_pow]
  simpa only [map_add, map_mul, map_pow, hx, hy, map_map_intCast, map_a₄Formal,
    map_a₆Formal] using weierstrass_equation

/-- The formal Tate coordinate equation specializes at every element other than zero
and one in an arbitrary field, with no characteristic restriction. -/
theorem specialized_weierstrass_equation {K : Type*} [Field K] (u : K)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    integralY u u⁻¹ (1 - u)⁻¹ ^ 2 +
        integralX u u⁻¹ (1 - u)⁻¹ * integralY u u⁻¹ (1 - u)⁻¹ =
      integralX u u⁻¹ (1 - u)⁻¹ ^ 3 +
        PowerSeries.map (Int.castRingHom K) a₄Formal * integralX u u⁻¹ (1 - u)⁻¹ +
        PowerSeries.map (Int.castRingHom K) a₆Formal := by
  have h := congrArg (PowerSeries.map (coordinateEval u hu0 hu1)) integral_weierstrass_equation
  simpa only [map_add, map_mul, map_pow, map_integralX, map_integralY, coordinateEval_u,
    coordinateEval_uInv, coordinateEval_oneSubInv, map_map_intCast] using h

end

end TateCurve
