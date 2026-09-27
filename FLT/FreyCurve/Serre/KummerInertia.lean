/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.RootsOfUnityInertia

/-!
# Tame Kummer inertia

Inertia fixes a unit whose power has invariant coefficients and whose exponent
is invertible in the residue field. Rescaling by a base-field element extends
this criterion to roots whose valuation belongs to the base value group.
-/

@[expose] public section

open Polynomial

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (A : ValuationSubring L) {n : ℕ}

/-- A unit with inertia-invariant prime-to-residue-characteristic power is fixed by inertia. -/
theorem inertia_fixes_unit_of_pow_fixed (hn : IsUnit (n : A))
    (σ : A.decompositionSubgroup K) (hσ : σ ∈ A.inertiaSubgroup K)
    (x : A) (hx : IsUnit x) (hpow : σ • (x ^ n) = x ^ n) : σ • x = x := by
  have hres : IsLocalRing.residue A (σ • x) = IsLocalRing.residue A x := by
    rw [IsLocalRing.ResidueField.residue_smul]
    exact congrArg (fun f : RingAut (IsLocalRing.ResidueField A) ↦
      f (IsLocalRing.residue A x)) hσ
  symm
  apply IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := X ^ n - C (x ^ n))
  · simp
  · simpa only [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero, ← smul_pow'] using hpow
  · rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    simp [map_sub, hres]
  · simpa only [derivative_sub, derivative_X_pow, derivative_C, eval_sub, eval_mul,
      eval_C, eval_natCast, eval_pow, eval_X, eval_zero, sub_zero] using hn.mul (hx.pow (n - 1))

/-- Tame Kummer roots with the valuation of a base-field element are fixed by inertia. -/
theorem inertia_fixes_of_pow_fixed_of_valuation_eq (hn : IsUnit (n : A))
    (σ : A.decompositionSubgroup K) (hσ : σ ∈ A.inertiaSubgroup K)
    {x : L} (hpow : (σ : L ≃ₐ[K] L) (x ^ n) = x ^ n)
    (b : Kˣ) (hval : A.valuation x = A.valuation (algebraMap K L (b : K))) :
    (σ : L ≃ₐ[K] L) x = x := by
  let c : L := algebraMap K L (b : K)
  have hc : c ≠ 0 := (_root_.map_ne_zero (algebraMap K L)).mpr b.ne_zero
  have hcfix : (σ : L ≃ₐ[K] L) c = c := (σ : L ≃ₐ[K] L).commutes _
  have hyval : A.valuation (x / c) = 1 := by
    rw [map_div₀, hval, div_self (A.valuation.ne_zero_iff.mpr hc)]
  let y : A := ⟨x / c, A.mem_of_valuation_le_one _ hyval.le⟩
  have hy : IsUnit y := (A.valuation_eq_one_iff y).mpr hyval
  have hypow : σ • (y ^ n) = y ^ n := by
    apply Subtype.ext
    change (σ : L ≃ₐ[K] L) ((x / c) ^ n) = (x / c) ^ n
    rw [div_pow, map_div₀, hpow, map_pow, hcfix]
  have hfix := congrArg Subtype.val (A.inertia_fixes_unit_of_pow_fixed hn σ hσ y hy hypow)
  change (σ : L ≃ₐ[K] L) (x / c) = x / c at hfix
  rw [map_div₀, hcfix] at hfix
  exact (div_left_inj' hc).mp hfix

/-- If the valuation of a base-field Kummer parameter is an `n`-th power in the
base value group, inertia fixes every root of every integral power of that parameter. -/
theorem inertia_fixes_of_pow_eq_zpow (hn : IsUnit (n : A))
    (σ : A.decompositionSubgroup K) (hσ : σ ∈ A.inertiaSubgroup K)
    (q b : Kˣ)
    (hval : A.valuation (algebraMap K L (q : K)) =
      A.valuation (algebraMap K L (b : K)) ^ n)
    (x : Lˣ) (m : ℤ) (hx : (x : L) ^ n = algebraMap K L (q : K) ^ m) :
    (σ : L ≃ₐ[K] L) (x : L) = x := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  apply A.inertia_fixes_of_pow_fixed_of_valuation_eq hn σ hσ
    (by rw [hx, map_zpow₀, AlgEquiv.commutes]) (b ^ m)
  apply (pow_left_inj₀ zero_le zero_le hn0).mp
  rw [← map_pow, hx, map_zpow₀, hval, ← zpow_natCast, ← zpow_natCast,
    ← zpow_mul, mul_comm (n : ℤ) m, zpow_mul]
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]

end ValuationSubring
