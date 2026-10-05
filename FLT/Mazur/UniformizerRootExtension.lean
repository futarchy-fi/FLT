/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.DiscreteValuationRing.EisensteinExtension

/-!
# Extensions adjoining a root of a uniformizer

The polynomial X^e-π is Eisenstein for every positive e. Its actual
polynomial quotient gives a finite extension of degree e and a DVR with
uniformizer ρ satisfying ρ^e=π. This supplies the ramified fields used to
scale short Weierstrass equations.
-/

@[expose] public section

namespace FLT.Mazur

open Polynomial IsLocalRing

universe u

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- A positive root of a uniformizer is defined by an Eisenstein polynomial. -/
theorem uniformizerRoot_isEisenstein {π : R} (hπ : Irreducible π) {e : ℕ} (he : 0 < e) :
    (X ^ e - C π).IsEisensteinAt (maximalIdeal R) := by
  apply (monic_X_pow_sub_C π (Nat.ne_of_gt he)).isEisensteinAt_of_mem_of_notMem
    (maximalIdeal.isMaximal R).ne_top
  · intro n hn
    rw [natDegree_X_pow_sub_C] at hn
    simp only [coeff_sub, coeff_X_pow, coeff_C, ite_eq_right (Nat.ne_of_lt hn), zero_sub]
    split_ifs
    · exact (maximalIdeal R).neg_mem hπ.not_isUnit
    · simp
  · simp only [coeff_sub, coeff_X_pow, coeff_C, ite_eq_right (Nat.ne_of_lt he),
      zero_sub, Ideal.neg_mem_iff]
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro h
    have hh : π ^ 2 ∣ π ^ 1 := by simpa using h
    have := (pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit).mp hh
    omega

variable {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]

/-- Construct the extension, its ring of integers, and its ramified uniformizer. -/
theorem exists_uniformizerRoot_extension {π : R} (hπ : Irreducible π)
    {e : ℕ} (he : 0 < e) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra R L) (_ : IsScalarTower R K L) (S : Type u) (_ : CommRing S)
      (_ : IsDomain S) (_ : IsDiscreteValuationRing S) (_ : Algebra R S)
      (_ : Module.Finite R S) (_ : Algebra S L) (_ : IsScalarTower R S L)
      (_ : IsFractionRing S L) (_ : IsIntegralClosure S R L) (ρ : S),
      Module.finrank K L = e ∧ Irreducible ρ ∧ ρ ^ e = algebraMap R S π ∧
        IsDiscreteValuationRing.addVal S (algebraMap R S π) = (e : ℕ∞) ∧
        Algebra.adjoin R {ρ} = ⊤ := by
  have hm := monic_X_pow_sub_C π (Nat.ne_of_gt he)
  have hd : (X ^ e - C π).natDegree = e := natDegree_X_pow_sub_C
  obtain ⟨L, hL, aK, fin, aR, towerK, S, hS, dom, dvr, aS, finS, aSL, towerS,
    frac, closure, ρ, hdeg, hρ, hroot, hval, hgen⟩ :=
    (uniformizerRoot_isEisenstein hπ he).existsTotallyRamifiedExtension
      (K := K) hm (by simpa only [hd] using he) hπ
  refine ⟨L, hL, aK, fin, aR, towerK, S, hS, dom, dvr, aS, finS, aSL, towerS,
    frac, closure, ρ, hdeg.trans hd, hρ, ?_, by simpa only [hd] using hval, hgen⟩
  simpa only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] using hroot

end FLT.Mazur
