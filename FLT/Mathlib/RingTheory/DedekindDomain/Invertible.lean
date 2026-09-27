/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.RingTheory.Noetherian.Basic
/-!
# Dedekind domains from invertible maximal ideals

In a Noetherian domain, invertibility of all maximal ideals implies invertibility
of every nonzero ideal. Ascending induction removes a maximal ideal factor;
Nakayama's lemma makes the remaining ideal strictly larger.
-/

@[expose] public section

open scoped nonZeroDivisors
open FractionalIdeal
variable {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
/-- In a Noetherian domain whose maximal ideals are invertible, every nonzero
integral ideal is invertible as a fractional ideal. -/
theorem Ideal.isUnit_coe_of_isUnit_maximals
    (h : ∀ M : Ideal R, M.IsMaximal → IsUnit (M : FractionalIdeal R⁰ K))
    (I : Ideal R) (hI : I ≠ ⊥) : IsUnit (I : FractionalIdeal R⁰ K) := by
  induction I using IsNoetherian.induction with
  | hgt I ih =>
    by_cases htop : I = ⊤
    · simp [htop]
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I htop
    obtain ⟨u, hu⟩ := h M hM
    have hJu : ↑u⁻¹ * (I : FractionalIdeal R⁰ K) ≤ 1 := by
      calc
        ↑u⁻¹ * (I : FractionalIdeal R⁰ K) ≤ ↑u⁻¹ * ↑u := by
          gcongr
          rw [hu]
          exact (coeIdeal_le_coeIdeal K).mpr hIM
        _ = 1 := u.inv_mul
    obtain ⟨J, hJ⟩ := le_one_iff_exists_coeIdeal.mp hJu
    have hIJ : I ≤ J := by
      apply (coeIdeal_le_coeIdeal K).mp
      calc
        (I : FractionalIdeal R⁰ K) = ↑u * (↑u⁻¹ * I) := by rw [← mul_assoc, u.mul_inv, one_mul]
        _ ≤ 1 * (↑u⁻¹ * I) := by
          gcongr
          rw [hu]
          exact coeIdeal_le_one
        _ = J := by rw [one_mul, ← hJ]
    have he : M * J = I := by
      apply coeIdeal_injective (K := K)
      change ((M * J : Ideal R) : FractionalIdeal R⁰ K) = (I : FractionalIdeal R⁰ K)
      rw [coeIdeal_mul, ← hu, hJ, ← mul_assoc, u.mul_inv, one_mul]
    have hlt : I < J := lt_of_le_of_ne hIJ (by
      intro hh
      have hmul : I ≤ M • I := by rw [Ideal.smul_eq_mul, hh, he, hh]
      obtain ⟨r, hr, hrI⟩ := Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul
        M I (IsNoetherian.noetherian I) hmul
      obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff I).mp hI
      have hr1 : r = 1 := mul_right_cancel₀ ha0 (by simpa using hrI a ha)
      exact hM.ne_top (Ideal.eq_top_of_isUnit_mem _ hr (hr1 ▸ isUnit_one)))
    have hJ0 : J ≠ ⊥ := ne_bot_of_le_ne_bot hI hIJ
    have hunit := (h M hM).mul (ih J hlt hJ0)
    rwa [← coeIdeal_mul, he] at hunit

/-- A Noetherian domain is Dedekind if all its maximal ideals are invertible
in a chosen fraction field. -/
theorem isDedekindDomain_of_isUnit_maximals
    (h : ∀ M : Ideal R, M.IsMaximal → IsUnit (M : FractionalIdeal R⁰ K)) :
    IsDedekindDomain R := by
  apply (isDedekindDomain_iff_mul_inv_cancel (K := K)).mpr
  intro I hI
  obtain ⟨a, J, ha, he⟩ := exists_eq_spanSingleton_mul I
  have hJ : J ≠ ⊥ := ideal_factor_ne_zero hI he
  have hu : IsUnit I := by
    rw [he]
    apply IsUnit.mul _ (Ideal.isUnit_coe_of_isUnit_maximals h J hJ)
    have haK : (algebraMap R K a)⁻¹ ≠ 0 := inv_ne_zero ((map_ne_zero_iff _
      (IsFractionRing.injective R K)).mpr ha)
    exact (coe_toPrincipalIdeal (R := R) (K := K) (Units.mk0 _ haK)) ▸
      (toPrincipalIdeal R K (Units.mk0 _ haK)).isUnit
  apply (FractionalIdeal.mul_inv_cancel_iff K).mpr
  obtain ⟨u, rfl⟩ := hu
  exact ⟨↑u⁻¹, u.mul_inv⟩
