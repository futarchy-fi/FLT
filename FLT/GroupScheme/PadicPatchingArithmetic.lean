/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Arithmetic for patching at a prime

The intersection of `ℤ[1/(dp)]` and `ℤ_p` inside `ℚ_p` is `ℤ[1/d]`, when `p` does
not divide `d`. These scalar statements are inputs to integral lattice patching.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable (p : ℕ) [Fact p.Prime]

/-- A `p`-integral element of `ℤ[1/(dp)]` comes from `ℤ[1/d]`.
The rings may be any realizations of the indicated localizations. -/
theorem exists_away_of_padic_integral (d : ℤ)
    (R S : Type*) [CommRing R] [CommRing S]
    [Algebra ℤ R] [Algebra ℤ S]
    [IsLocalization.Away d R] [IsLocalization.Away (d * p) S]
    [Algebra R ℚ_[p]] [Algebra S ℚ_[p]]
    (x : S) (hx : ‖algebraMap S ℚ_[p] x‖ ≤ 1) :
    ∃ r : R, algebraMap R ℚ_[p] r = algebraMap S ℚ_[p] x := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (d * p) x
  have he : algebraMap S ℚ_[p] x * ((d : ℚ_[p]) * p) ^ n = a := by
    simpa using congrArg (algebraMap S ℚ_[p]) ha
  let y : ℤ_[p] := ⟨algebraMap S ℚ_[p] x, hx⟩
  have hdvd : (p : ℤ_[p]) ^ n ∣ (a : ℤ_[p]) := by
    refine ⟨y * (d : ℤ_[p]) ^ n, ?_⟩
    apply PadicInt.ext
    change (a : ℚ_[p]) = (p : ℚ_[p]) ^ n * (algebraMap S ℚ_[p] x * (d : ℚ_[p]) ^ n)
    rw [← he, mul_pow]
    ring
  obtain ⟨b, hb⟩ := (PadicInt.pow_p_dvd_int_iff n a).mp hdvd
  have hp : (p : ℚ_[p]) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hd : algebraMap S ℚ_[p] x * (d : ℚ_[p]) ^ n = b := by
    apply mul_right_cancel₀ hp
    rw [mul_assoc, ← mul_pow, he, hb]
    push_cast
    ring
  let r : R := IsLocalization.mk' R b (⟨d ^ n, n, rfl⟩ : Submonoid.powers d)
  have hr : r * algebraMap ℤ R (d ^ n) = algebraMap ℤ R b :=
    IsLocalization.mk'_spec _ _ _
  have hr' : algebraMap R ℚ_[p] r * (d : ℚ_[p]) ^ n = b := by
    simpa using congrArg (algebraMap R ℚ_[p]) hr
  have hd0 : (d : ℚ_[p]) ^ n ≠ 0 := by
    have hu := (IsLocalization.Away.algebraMap_pow_isUnit (S := R) d n).map
      (algebraMap R ℚ_[p])
    simpa using hu.ne_zero
  exact ⟨r, mul_right_cancel₀ hd0 (hr'.trans hd.symm)⟩

/-- Elements of `ℤ[1/d]` are `p`-integral when `p` does not divide `d`. -/
theorem away_padic_integral (d : ℤ) (hd : ¬ (p : ℤ) ∣ d)
    (R : Type*) [CommRing R] [Algebra ℤ R] [IsLocalization.Away d R]
    [Algebra R ℚ_[p]] (x : R) : ‖algebraMap R ℚ_[p] x‖ ≤ 1 := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj d x
  have he : algebraMap R ℚ_[p] x * (d : ℚ_[p]) ^ n = a := by
    simpa using congrArg (algebraMap R ℚ_[p]) ha
  have hd1 : ‖(d : ℚ_[p])‖ = 1 := by
    exact le_antisymm (PadicInt.norm_le_one (d : ℤ_[p]))
      (le_of_not_gt (mt (PadicInt.norm_int_lt_one_iff_dvd d).mp hd))
  have hn := congrArg norm he
  rw [norm_mul, norm_pow, hd1, one_pow, mul_one] at hn
  rw [hn]
  exact PadicInt.norm_le_one (a : ℤ_[p])

/-- The scalar intersection used in patching: `ℤ[1/(dp)] ∩ ℤ_p = ℤ[1/d]`. -/
theorem away_padic_intersection (d : ℤ) (hd : ¬ (p : ℤ) ∣ d)
    (R S : Type*) [CommRing R] [CommRing S]
    [Algebra ℤ R] [Algebra ℤ S]
    [IsLocalization.Away d R] [IsLocalization.Away (d * p) S]
    [Algebra R ℚ_[p]] [Algebra S ℚ_[p]] (x : S) :
    ‖algebraMap S ℚ_[p] x‖ ≤ 1 ↔
      ∃ r : R, algebraMap R ℚ_[p] r = algebraMap S ℚ_[p] x := by
  refine ⟨exists_away_of_padic_integral p d R S x, ?_⟩
  rintro ⟨r, hr⟩
  rw [← hr]
  exact away_padic_integral p d hd R r

/-- Every `p`-adic number becomes integral after multiplication by a power of `p`. -/
theorem padic_exists_pow_mul_integral (x : ℚ_[p]) :
    ∃ n : ℕ, ‖x * (p : ℚ_[p]) ^ n‖ ≤ 1 := by
  by_cases hx : ‖x‖ ≤ 1
  · exact ⟨0, by simpa using hx⟩
  let n := (-x.valuation).toNat
  have hn : (n : ℤ) = -x.valuation := by
    apply Int.toNat_of_nonneg
    rw [Padic.norm_le_one_iff_val_nonneg, not_le] at hx
    exact neg_nonneg.mpr hx.le
  have hx0 : x ≠ 0 := by
    intro h
    simp [h] at hx
  refine ⟨n, le_of_eq ?_⟩
  rw [norm_mul, Padic.norm_p_pow, Padic.norm_eq_zpow_neg_valuation hx0,
    ← zpow_add', hn, neg_neg, neg_add_cancel, zpow_zero]
  exact Or.inl (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

/-- The fraction field of `ℤ_p` is already obtained by inverting `p`. -/
theorem padic_isLocalization_away : IsLocalization.Away (p : ℤ_[p]) ℚ_[p] := by
  apply IsLocalization.Away.mk
  · exact isUnit_iff_ne_zero.mpr (by
      simpa using (show (p : ℚ_[p]) ≠ 0 by
        exact_mod_cast (Fact.out : p.Prime).ne_zero))
  · intro x
    obtain ⟨n, hn⟩ := padic_exists_pow_mul_integral p x
    exact ⟨n, ⟨x * (p : ℚ_[p]) ^ n, hn⟩, rfl⟩
  · intro a b hab
    exact ⟨0, by simpa using PadicInt.ext hab⟩

/-- `ℤ[1/(dp)]` approximates every `p`-adic number modulo `p^k ℤ_p`.
This is the additive approximation input to lattice patching. -/
theorem exists_away_add_padic (d : ℤ) (S : Type*) [CommRing S]
    [Algebra ℤ S] [IsLocalization.Away (d * p) S] [Algebra S ℚ_[p]]
    (x : ℚ_[p]) (k : ℕ) :
    ∃ s : S, ∃ o : ℤ_[p], x = algebraMap S ℚ_[p] s + (p : ℚ_[p]) ^ k * o := by
  obtain ⟨n, hn⟩ := padic_exists_pow_mul_integral p x
  let y : ℤ_[p] := ⟨x * (p : ℚ_[p]) ^ n, hn⟩
  obtain ⟨o, ho⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec (n + k) y)
  have he : x * (p : ℚ_[p]) ^ n - (y.appr (n + k) : ℚ_[p]) =
      (p : ℚ_[p]) ^ (n + k) * o := by
    exact congrArg (fun z : ℤ_[p] ↦ (z : ℚ_[p])) ho
  have hu : IsUnit (p : S) := by
    simpa using IsLocalization.Away.isUnit_of_dvd (S := S) (x := d * (p : ℤ))
      (show (p : ℤ) ∣ d * p from dvd_mul_left _ _)
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hv' : (p : ℚ_[p]) * algebraMap S ℚ_[p] v = 1 := by
    simpa using congrArg (algebraMap S ℚ_[p]) hv
  refine ⟨(y.appr (n + k) : S) * v ^ n, o, ?_⟩
  have hp : (p : ℚ_[p]) ^ n ≠ 0 := pow_ne_zero _ (by
    exact_mod_cast (Fact.out : p.Prime).ne_zero)
  apply mul_right_cancel₀ hp
  simp only [map_mul, map_natCast, map_pow, add_mul, mul_assoc]
  have hvn : algebraMap S ℚ_[p] v ^ n * (p : ℚ_[p]) ^ n = 1 := by
    rw [← mul_pow, mul_comm, hv', one_pow]
  rw [hvn, mul_one]
  rw [pow_add] at he
  linear_combination he

end ThreeAdicPlan
