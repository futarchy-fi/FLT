/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.InvariantLogarithmic
public import FLT.EllipticCurve.MultiplicationDifferential
/-!
# The universal division-polynomial differential identity

The invariant differential calculation for multiplication determines the second
logarithmic derivative of the difference of two multiplication coordinates.
The elliptic divisibility sequence addition law then gives a recurrence for the
second logarithmic derivatives of the division functions. The cases one and two
start the recurrence. Applying it to squared division polynomials proves that
the corrected differential defect vanishes, including at even indices.
-/

@[expose] public section

namespace WeierstrassCurve.Universal
open Polynomial

/-- The mixed logarithmic identity for the universal point and its `n`th multiple. -/
lemma logSecond_smulX_sub (n : ℕ) (hn : 2 ≤ n) :
    invD.logSecond (Affine.smulX n - Affine.smulX 1) =
       - (((n : Universal.Field) + 1) ^ 2 * Affine.smulX ((n : ℤ) + 1) + 
        ((n : Universal.Field) - 1) ^ 2 * Affine.smulX ((n : ℤ) - 1) - 
        2 * (n : Universal.Field) ^ 2 * Affine.smulX n - 2 * Affine.smulX 1) := by
  classical
  have hx : Affine.smulX n ≠ Affine.smulX 1 :=
    Affine.smulX_ne_smulX (by omega) (by omega)
  have hxp := smul_add_coordinates (m := n) (n := 1) (by omega) one_ne_zero (by omega) hx
  have hxm := smul_add_coordinates (m := n) (n := - 1) (by omega) (by omega) (by omega)
    (by simpa only [Affine.smulX_neg] using hx)
  simp only [Affine.smulX_neg, Affine.smulY_neg one_ne_zero, ← sub_eq_add_neg] at hxm
  have hd := pointedCurve.toAffine.logSecond_sub invD
    (Affine.nonsingular_smulX_smulY (n := n) (by omega)).1
    (Affine.nonsingular_smulX_smulY (n := 1) one_ne_zero).1 hx
    (invD_coeff _) (invD_coeff _) (invD.map_natCast n) invD.map_one_eq_zero
    (invD_smul n (by omega)).1 (invD_smul n (by omega)).2
    (m := (n : Universal.Field)) (n := 1) (by simpa using invD_x) (by simpa using invD_y)
  dsimp only at hxp hxm hd
  rw [← hxp.1, ← hxm.1] at hd
  simpa only [one_pow, mul_one] using hd

/-- The second logarithmic derivative of the two-division function. -/
lemma logSecond_ψ₂ : invD.logSecond (ψᵤ 2) =
    4 * (Affine.smulX 1 - Affine.smulX 2) := by
  have h := congrArg xToField curve.Ψ₂Sq_mul_derivative_invar_sub
  simp only [map_sub, map_mul, map_pow, map_ofNat,
    show xToField curve.Ψ₂Sq = ψᵤ 2 ^ 2 from polyToField_ψ₂Sq] at h
  rw [invD.logSecond_eq, invD_ψ₂]
  have hdd : invD (xToField curve.invar) = ψᵤ 2 * xToField curve.invar.derivative := by
    simpa only [xToField, RingHom.comp_apply, ψᵤ, ψ_two] using invD_C curve.invar
  rw [hdd]
  have hnum : ψᵤ 2 * (ψᵤ 2 * xToField curve.invar.derivative) - 
      xToField curve.invar ^ 2 = 4 * xToField curve.Ψ₃ := by
    linear_combination h
  rw [hnum, Affine.smulX_two]
  have hc : ψᵤ 3 = xToField curve.Ψ₃ := by
    simp only [ψᵤ, ψ_three, xToField, RingHom.comp_apply]
  rw [hc, sub_sub_cancel, mul_div_assoc]

/-- The second logarithmic derivative of every nonzero division function. -/
lemma logSecond_ψ (n : ℕ) (hn : n ≠ 0) :
    invD.logSecond (ψᵤ n) = (n : Universal.Field) ^ 2 * 
      (Affine.smulX 1 - Affine.smulX n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain _|_|_|n := n
    · exact (hn rfl).elim
    · simp [ψᵤ, Derivation.logSecond]
    · simpa only [Nat.reduceAdd, Nat.cast_ofNat, show (2 : Universal.Field) ^ 2 = 4 by norm_num]
        using logSecond_ψ₂
    · let k : ℕ := n + 2
      have hkm : ((k : ℤ) - 1) = (n + 1 : ℕ) := by dsimp [k]; omega
      have hkp : ((k : ℤ) + 1) = (n + 1 + 1 + 1 : ℕ) := by dsimp [k]; omega
      have he : Affine.smulX k - Affine.smulX 1 =
           - (ψᵤ ((k : ℤ) + 1) * ψᵤ ((k : ℤ) - 1)/ψᵤ k ^ 2) := by
        rw [Affine.smulX_eq (by dsimp [k]; omega)]
        ring
      have h := logSecond_smulX_sub k (by dsimp [k]; omega)
      rw [he, invD.logSecond_neg, invD.logSecond_div
        (mul_ne_zero (ψᵤ_ne_zero (by dsimp [k]; omega))
          (ψᵤ_ne_zero (by dsimp [k]; omega)))
        (pow_ne_zero 2 (ψᵤ_ne_zero (by dsimp [k]; omega))),
        invD.logSecond_mul (ψᵤ_ne_zero (by dsimp [k]; omega))
          (ψᵤ_ne_zero (by dsimp [k]; omega)),
        invD.logSecond_sq (ψᵤ_ne_zero (by dsimp [k]; omega)), hkm, hkp,
        ih (n + 1) (by omega) (by omega), ih k (by dsimp [k]; omega) (by dsimp [k]; omega)] at h
      dsimp [k] at h
      push_cast at h ⊢
      linear_combination h

/-- The polynomial differential numerator represents the negative second
logarithmic derivative in the universal function field. -/
lemma logSecond_polynomial (f : (MvPolynomial Coeff ℤ)[X]) (hf : xToField f ≠ 0) :
    invD.logSecond (xToField f) * xToField f ^ 2 = -xToField (curve.divisionDifferential f) := by
  have hd (g : (MvPolynomial Coeff ℤ)[X]) :
      invD (xToField g) = ψᵤ 2 * xToField g.derivative := by
    simpa only [xToField, RingHom.comp_apply, ψᵤ, ψ_two] using invD_C g
  rw [invD.logSecond_eq, div_mul_cancel₀ _ (pow_ne_zero 2 hf), hd]
  simp only [invD.leibniz, invD_ψ₂, hd, smul_eq_mul,
    divisionDifferential, map_sub, map_mul, map_pow,
    show xToField curve.Ψ₂Sq = ψᵤ 2 ^ 2 from polyToField_ψ₂Sq]
  ring

/-- The corrected division-polynomial differential identity holds at every
natural index on the universal curve. -/
lemma divisionDifferentialDefect_all (n : ℕ) : curve.divisionDifferentialDefect n = 0 := by
  obtain rfl | hn := eq_or_ne n 0
  · exact curve.divisionDifferentialDefect_zero
  have hp : ψᵤ n ≠ 0 := ψᵤ_ne_zero (by exact_mod_cast hn)
  have hq : xToField (curve.ΨSq n) ≠ 0 := by rw [xToField_ΨSq]; exact pow_ne_zero 2 hp
  have hl := logSecond_polynomial (curve.ΨSq n) hq
  rw [xToField_ΨSq, invD.logSecond_sq hp, logSecond_ψ n hn] at hl
  have hφ : xToField (curve.Φ n) = Affine.smulX n * ψᵤ n ^ 2 := by
    rw [xToField_Φ, Affine.smulX, div_mul_cancel₀ _ (pow_ne_zero 2 hp)]
  have hd := congrArg xToField (curve.divisionDifferential_ΨSq n)
  simp only [map_sub, map_mul, map_pow, map_ofNat, xToField_ΨSq, hφ,
    show xToField X = Affine.smulX 1 from Affine.smulX_one.symm] at hd
  have hc : xToField (C (((n : ℤ) : MvPolynomial Coeff ℤ))) = (n : Universal.Field) := by
    simp only [Int.cast_natCast, map_natCast]
  rw [hc] at hd
  have hz : 2 * ψᵤ n ^ 2 * xToField (curve.divisionDifferentialDefect n) = 0 := by
    linear_combination hl - hd
  apply xToField_injective
  rw [map_zero]
  exact (mul_eq_zero.mp hz).resolve_left
    (mul_ne_zero Universal.Field.two_ne_zero (pow_ne_zero 2 hp))

end WeierstrassCurve.Universal

namespace WeierstrassCurve

/-- The corrected division-polynomial differential identity holds over every
commutative ring, by specialization from the universal curve. -/
theorem divisionDifferentialDefect_eq_zero {R : Type*} [CommRing R]
    (E : WeierstrassCurve R) (n : ℕ) : E.divisionDifferentialDefect n = 0 :=
  E.divisionDifferentialDefect_eq_zero_of_universal (Universal.divisionDifferentialDefect_all n)

end WeierstrassCurve
