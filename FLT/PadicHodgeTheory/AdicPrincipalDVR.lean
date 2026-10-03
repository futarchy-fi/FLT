/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # A separated local ring with regular principal maximal ideal is a DVR -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable {R : Type*} [CommRing R]
variable (t : R)
variable [IsHausdorff (Ideal.span {t}) R]

/-- Adic separatedness makes the t-divisibility order of every nonzero element finite. -/
theorem adicParameter_finiteMultiplicity {x : R} (hx : x ≠ 0) : FiniteMultiplicity t x := by
  by_contra hf
  apply hx
  apply IsHausdorff.haus' (I := Ideal.span {t})
  intro n
  have hd : t ^ n ∣ x := by
    cases n with
    | zero => simp
    | succ n => by_contra hn; exact hf ⟨n, hn⟩
  simpa only [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] using hd

variable [IsLocalRing R] (hmax : IsLocalRing.maximalIdeal R = Ideal.span {t})
include hmax

/-- Every nonzero element is a unit times a finite power of the parameter. -/
theorem adicParameter_factor {x : R} (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : Rˣ), x = t ^ n * u := by
  obtain ⟨c, hc, hnot⟩ := (adicParameter_finiteMultiplicity t hx).exists_eq_pow_mul_and_not_dvd
  have hu : IsUnit c := by
    by_contra hn
    apply hnot
    rw [← Ideal.mem_span_singleton, ← hmax]
    exact hn
  exact ⟨multiplicity t x, hu.unit, by simpa only [IsUnit.unit_spec] using hc⟩

/-- A regular parameter and unit-times-power factorizations exclude zero divisors. -/
theorem adicParameter_noZeroDivisors
    (hreg : ∀ x : R, t * x = 0 → x = 0) : NoZeroDivisors R := by
  have hpow (n : ℕ) (x : R) : t ^ n * x = 0 → x = 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      intro h
      apply ih
      apply hreg
      simpa only [pow_succ', mul_assoc] using h
  constructor
  intro x y hxy
  by_cases hx : x = 0
  · exact Or.inl hx
  by_cases hy : y = 0
  · exact Or.inr hy
  obtain ⟨n, u, rfl⟩ := adicParameter_factor t hmax hx
  obtain ⟨m, v, rfl⟩ := adicParameter_factor t hmax hy
  have h : (u * v : Rˣ).val = 0 := by
    apply hpow (n + m)
    simpa only [Units.val_mul, pow_add, mul_mul_mul_comm] using hxy
  exact False.elim ((u * v).ne_zero h)

/-- The actual regularity hypothesis yields the domain structure. -/
theorem adicParameter_isDomain (hreg : ∀ x : R, t * x = 0 → x = 0) : IsDomain R := by
  let : NoZeroDivisors R := adicParameter_noZeroDivisors t hmax hreg
  exact NoZeroDivisors.to_isDomain R

/-- Once the domain is established, the same parameter gives the DVR structure. -/
theorem adicParameter_isDiscreteValuationRing [IsDomain R] (ht : t ≠ 0) :
    IsDiscreteValuationRing R := by
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨t, IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal t ht hmax, ?_⟩
  intro x hx
  obtain ⟨n, u, hu⟩ := adicParameter_factor t hmax hx
  exact ⟨n, ⟨u, hu.symm⟩⟩

end PadicHodgeTheory
