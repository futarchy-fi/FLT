/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.NiveauTwoInertiaGenerator
public import Mathlib.Algebra.Ring.GeomSum

/-!
# Higher-niveau generators and their actual cyclotomic norms

For any positive niveau, choose a full root-character generator first. Its
geometric-sum norm is the actual cyclotomic value, of order p−1. This does
not supply higher-coefficient-field representation weights or their spectrum.
-/

@[expose] public noncomputable section
namespace LocalRoot
open IsLocalRing

variable (p : ℕ) [Fact p.Prime]
local notation "v" => LocalCyclotomic.rationalPlace p
local notation "Kv" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v
local notation "O" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "Ω" => AlgebraicClosure Kv
local notation "k" => ResidueField (IntegralClosure O Ω)
attribute [local instance] rationalResidue_charP

/-- The norm exponent converts any positive niveau root character to cyclotomic. -/
theorem character_niveau_norm_eq_residueCyclotomic {r : ℕ} (hr : 0 < r) {π : O}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α : Ω} (hn : 0 < p ^ r - 1)
    (hα : α ^ (p ^ r - 1) = algebraMap Kv Ω π.1) (σ : localInertiaGroup v) :
    character v hn
      (fun h ↦ IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero
        hπ (Subtype.ext h)) hα σ ^ (∑ i ∈ Finset.range r, p ^ i) = residueCyclotomic p σ := by
  have hp := (Fact.out : p.Prime).one_lt
  have h1 : 0 < p - 1 := by omega
  have hd : (p - 1) * (∑ i ∈ Finset.range r, p ^ i) = p ^ r - 1 := by
    rw [mul_comm]
    exact geom_sum_mul_of_one_le (by omega : 1 ≤ p) r
  have hm : 0 < ∑ i ∈ Finset.range r, p ^ i := by
    exact Finset.sum_pos (fun i _ ↦ pow_pos (by omega) i)
      ⟨0, Finset.mem_range.mpr hr⟩
  have hα' : α ^ ((p - 1) * (∑ i ∈ Finset.range r, p ^ i)) = algebraMap Kv Ω π.1 := by
    rwa [hd]
  have h := character_degree_mul v h1
    (fun h ↦ IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero
      hπ (Subtype.ext h)) _ hm hα' σ
  rw [character_one_eq_residueCyclotomic p hπ h1] at h
  simpa only [hd] using h

/-- Every positive niveau has a full generator whose actual cyclotomic norm generates. -/
theorem exists_niveau_inertia_generator {r : ℕ} (hr : 0 < r) {π : O}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α : Ω} (hn : 0 < p ^ r - 1)
    (hα : α ^ (p ^ r - 1) = algebraMap Kv Ω π.1) :
    ∃ σ : localInertiaGroup v,
      let z := character v hn
        (fun h ↦ IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero
          hπ (Subtype.ext h)) hα σ
      orderOf z = p ^ r - 1 ∧
      z ^ (∑ i ∈ Finset.range r, p ^ i) = residueCyclotomic p σ ∧
      orderOf (modCyclotomic p σ.1) = p - 1 := by
  have hp := (Fact.out : p.Prime).one_lt
  have hnk : ((p ^ r - 1 : ℕ) : k) ≠ 0 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p ^ r), Nat.cast_pow, Nat.cast_one,
      CharP.cast_eq_zero k p, zero_pow hr.ne', zero_sub]
    exact neg_ne_zero.mpr one_ne_zero
  obtain ⟨σ, hσ⟩ := exists_rootCharacter_generator v hn hnk hπ hα
  have hc := character_niveau_norm_eq_residueCyclotomic p hr hπ hn hα σ
  refine ⟨σ, hσ, hc, ?_⟩
  have hd : (p - 1) * (∑ i ∈ Finset.range r, p ^ i) = p ^ r - 1 := by
    rw [mul_comm]
    exact geom_sum_mul_of_one_le (by omega : 1 ≤ p) r
  have hm : (∑ i ∈ Finset.range r, p ^ i) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hd
    omega
  rw [← residueCyclotomic_order p σ, ← hc,
    orderOf_pow_of_dvd hm (by rw [hσ, ← hd]; exact dvd_mul_left _ _),
    hσ, ← hd, Nat.mul_div_left _ (Nat.pos_of_ne_zero hm)]

end LocalRoot
