/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.Algebra.Polynomial.Taylor

/-! # Local irreducibility of the p-power cyclotomic polynomials -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
open Polynomial
variable (p : ℕ) [hp : Fact p.Prime]

/-- Integer p-power divisibility is preserved and reflected by the actual Z_p embedding. -/
theorem padicInt_intCast_mem_primeIdeal_pow (z : ℤ) (n : ℕ) :
    (z : ℤ_[p]) ∈ (Ideal.span {(p : ℤ_[p])}) ^ n ↔
      z ∈ (Ideal.span {(p : ℤ)}) ^ n := by
  rw [Ideal.span_singleton_pow, ← PadicInt.norm_le_pow_iff_mem_span_pow,
    PadicInt.norm_int_le_pow_iff_dvd, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/-- A monic integer Eisenstein polynomial remains Eisenstein over the actual p-adic integers. -/
theorem padicInt_monic_eisenstein_map (f : ℤ[X]) (hf : f.Monic)
    (he : f.IsEisensteinAt (Ideal.span {(p : ℤ)})) :
    (f.map (Int.castRingHom ℤ_[p])).IsEisensteinAt (Ideal.span {(p : ℤ_[p])}) := by
  apply (hf.map _).isEisensteinAt_of_mem_of_notMem
    (by rw [← PadicInt.maximalIdeal_eq_span_p]; exact Ideal.IsPrime.ne_top inferInstance)
  · intro i hi
    rw [coeff_map]
    change (f.coeff i : ℤ_[p]) ∈ _
    have hmem := he.mem (by simpa only [hf.natDegree_map] using hi)
    simpa only [pow_one] using (padicInt_intCast_mem_primeIdeal_pow p (f.coeff i) 1).mpr
      (by simpa only [pow_one] using hmem)
  · rw [coeff_map]
    exact fun h ↦ he.notMem ((padicInt_intCast_mem_primeIdeal_pow p (f.coeff 0) 2).mp h)

/-- The shifted local cyclotomic polynomial is Eisenstein at p. -/
theorem padicInt_cyclotomic_eisenstein (s : ℕ) :
    ((cyclotomic (p ^ (s + 1)) ℤ_[p]).comp (X + 1)).IsEisensteinAt
      (Ideal.span {(p : ℤ_[p])}) := by
  have hm : ((cyclotomic (p ^ (s + 1)) ℤ).comp (X + 1)).Monic := by
    simpa using (cyclotomic.monic (p ^ (s + 1)) ℤ).comp (monic_X_add_C 1)
      (by simp : (X + C (1 : ℤ)).natDegree ≠ 0)
  simpa only [map_comp, map_cyclotomic, Polynomial.map_add, map_X, Polynomial.map_one] using
    padicInt_monic_eisenstein_map p _ hm
      (cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p s)

/-- The p-power cyclotomic polynomial is irreducible over Q_p, including p = 2. -/
theorem padic_cyclotomic_primePower_irreducible (s : ℕ) :
    Irreducible (cyclotomic (p ^ (s + 1)) ℚ_[p]) := by
  have hm : ((cyclotomic (p ^ (s + 1)) ℤ_[p]).comp (X + 1)).Monic := by
    simpa using (cyclotomic.monic (p ^ (s + 1)) ℤ_[p]).comp (monic_X_add_C 1)
      (by simp : (X + C (1 : ℤ_[p])).natDegree ≠ 0)
  have hi := (padicInt_cyclotomic_eisenstein p s).irreducible
    (by rw [← PadicInt.maximalIdeal_eq_span_p]; infer_instance) hm.isPrimitive
    (by
      rw [natDegree_comp, natDegree_cyclotomic, show (X + 1 : ℤ_[p][X]) = X + C 1 by simp,
        natDegree_X_add_C, mul_one]
      exact Nat.totient_pos.mpr (pow_pos hp.out.pos _))
  have hq := (hm.irreducible_iff_irreducible_map_fraction_map (K := ℚ_[p])).mp hi
  have ht : Irreducible ((taylorEquiv (1 : ℚ_[p])) (cyclotomic (p ^ (s + 1)) ℚ_[p])) := by
    change Irreducible ((cyclotomic (p ^ (s + 1)) ℚ_[p]).comp (X + C 1))
    simpa only [map_comp, map_cyclotomic,
      Polynomial.map_add, map_X, Polynomial.map_one, C_1] using hq
  exact (MulEquiv.irreducible_iff (taylorEquiv (1 : ℚ_[p])).toMulEquiv).mp ht

end PadicHodgeTheory
