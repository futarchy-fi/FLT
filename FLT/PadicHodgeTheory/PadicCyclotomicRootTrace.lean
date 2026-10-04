/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.PadicCyclotomicRelativeMinpoly
public import FLT.PadicHodgeTheory.PadicCyclotomicTrace

/-! # Actual normalized traces of cyclotomic roots -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
open Polynomial
variable (p : ℕ) [hp : Fact p.Prime]

/-- A primitive root strictly above a positive target level has normalized trace zero. -/
theorem padicCyclotomicTrace_primitive_eq_zero (n r : ℕ) (ζ : PadicAlgCl p)
    (hζ : IsPrimitiveRoot ζ (p ^ (n + (r + 1) + 1))) :
    padicCyclotomicTrace p (n + 1) ζ = 0 := by
  have hd : 1 < p ^ (r + 1) := one_lt_pow₀ hp.out.one_lt (by omega)
  change Algebra.normalizedTrace _ _ ζ = 0
  rw [Algebra.normalizedTrace_minpoly, padicCyclotomicRelative_minpoly p n (r + 1) ζ hζ]
  have hc (c : padicCyclotomicTower p (n + 1)) :
      (X ^ (p ^ (r + 1)) - C c).nextCoeff = 0 := by
    rw [nextCoeff, natDegree_X_pow_sub_C]
    simp [coeff_sub, coeff_X_pow, coeff_C, show p ^ (r + 1) - 1 ≠ 0 by omega,
      show p ^ (r + 1) - 1 ≠ p ^ (r + 1) by omega]
  rw [hc, neg_zero, smul_zero]

open Classical in
/-- Every p-power root is either fixed by the target projection or killed by it. -/
theorem padicCyclotomicProjection_root (n m : ℕ) (ζ : PadicAlgCl p)
    (hζ : ζ ^ (p ^ m) = 1) :
    padicCyclotomicProjection p (n + 1) ζ =
      if ζ ^ (p ^ (n + 1)) = 1 then ζ else 0 := by
  split_ifs with h
  · exact congrArg Subtype.val (padicCyclotomicTrace_coe p (n + 1)
      ⟨ζ, padicCyclotomicTower_root_mem p (n + 1) ζ h⟩)
  · obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hζ)
    have hprim : IsPrimitiveRoot ζ (p ^ k) := hk ▸ IsPrimitiveRoot.orderOf ζ
    have hnk : n + 1 < k := by
      by_contra! hle
      apply h
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      rw [hd, pow_add, pow_mul, hprim.pow_eq_one, one_pow]
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (show n + 2 ≤ k by omega)
    have he : k = n + (r + 1) + 1 := by omega
    rw [he] at hprim
    rw [padicCyclotomicProjection_apply, padicCyclotomicTrace_primitive_eq_zero p n r ζ hprim]
    rfl

/-- Root powers have trace zero unless their exponent is divisible by the relative degree. -/
theorem padicCyclotomicProjection_root_pow (n r i : ℕ) (ζ : PadicAlgCl p)
    (hζ : IsPrimitiveRoot ζ (p ^ (n + r + 1))) :
    padicCyclotomicProjection p (n + 1) (ζ ^ i) =
      if p ^ r ∣ i then ζ ^ i else 0 := by
  rw [padicCyclotomicProjection_root p n (n + r + 1) (ζ ^ i)
    (by rw [← pow_mul, Nat.mul_comm i, pow_mul, hζ.pow_eq_one, one_pow])]
  congr 1
  rw [← pow_mul, hζ.pow_eq_one_iff_dvd]
  have he : p ^ (n + r + 1) = p ^ r * p ^ (n + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [he, Nat.mul_dvd_mul_iff_right (pow_pos hp.out.pos (n + 1))]

end PadicHodgeTheory
