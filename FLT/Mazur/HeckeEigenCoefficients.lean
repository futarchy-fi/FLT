/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic

/-!
# The first coefficient in Mazur's formal-immersion argument

The coefficient argument in Mazur (1978), Proposition 3.1: the weight-two
Hecke eigenrelations away from the level, and the U relation at the level,
force a cuspidal expansion with vanishing first coefficient to vanish.
For a nonzero space carrying these actions, injectivity of the expansion
makes the first-coefficient functional surjective without choosing eigenvectors.

This is the algebraic recurrence step over an arbitrary coefficient ring.
It does not construct modular curves, Hecke actions on differentials, the
q-expansion principle, or a formal immersion.
-/

@[expose] public section

namespace FLT.Mazur

/-- Prime-index Hecke recurrences determine whether a cuspidal sequence vanishes.
The level need not be prime for this purely algebraic implication. -/
theorem eq_zero_of_hecke_relations {R : Type*} [Ring R]
    (a c : ℕ → R) (N : ℕ) (hzero : a 0 = 0) (hone : a 1 = 0)
    (hU : ∀ m, a (N * m) = c N * a m)
    (hT : ∀ l, l.Prime → l ≠ N → ∀ m,
      a (l * m) = c l * a m - if l ∣ m then (l : R) * a (m / l) else 0) :
    a = 0 := by
  funext n
  change a n = 0
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · simpa [hn0] using hzero
    by_cases hn1 : n = 1
    · simpa [hn1] using hone
    obtain ⟨l, hl, hln⟩ := Nat.exists_prime_and_dvd hn1
    have hm : n / l < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) hl.one_lt
    have hmm : n / l / l < n := lt_of_le_of_lt (Nat.div_le_self _ _) hm
    have heq : l * (n / l) = n := Nat.mul_div_cancel' hln
    by_cases hlN : l = N
    · have h := hU (n / l)
      rw [← hlN, heq, ih _ hm, mul_zero] at h
      exact h
    · have h := hT l hl hlN (n / l)
      rw [heq, ih _ hm, ih _ hmm] at h
      simpa using h

/-- A nonzero cuspidal power series satisfying the eigenrelations has nonzero
first coefficient, including in positive characteristic. -/
theorem coeff_one_ne_zero_of_hecke_relations {R : Type*} [Ring R]
    (f : PowerSeries R) (c : ℕ → R) (N : ℕ)
    (hf : f ≠ 0) (hzero : f.coeff 0 = 0)
    (hU : ∀ m, f.coeff (N * m) = c N * f.coeff m)
    (hT : ∀ l, l.Prime → l ≠ N → ∀ m,
      f.coeff (l * m) = c l * f.coeff m -
        if l ∣ m then (l : R) * f.coeff (m / l) else 0) :
    f.coeff 1 ≠ 0 := by
  intro hone
  have h := eq_zero_of_hecke_relations (fun n ↦ f.coeff n) c N hzero hone hU hT
  apply hf
  ext n
  simpa using congrFun h n

/-- A nonzero space with an injective cuspidal expansion and the prime Hecke
coefficient formulas has a vector with nonzero first coefficient. This avoids
choosing simultaneous eigenvectors or extending the coefficient field. -/
theorem exists_coeff_one_ne_zero_of_hecke_action
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Nontrivial V]
    (q : V →ₗ[K] PowerSeries K) (hq : Function.Injective q)
    (N : ℕ) (U : V →ₗ[K] V) (T : ℕ → V →ₗ[K] V)
    (hzero : ∀ v, (q v).coeff 0 = 0)
    (hU : ∀ v m, (q v).coeff (N * m) = (q (U v)).coeff m)
    (hT : ∀ l, l.Prime → l ≠ N → ∀ v m,
      (q v).coeff (l * m) = (q (T l v)).coeff m -
        if l ∣ m then (l : K) * (q v).coeff (m / l) else 0) :
    ∃ v, (q v).coeff 1 ≠ 0 := by
  by_contra h
  push Not at h
  have hall : ∀ n v, (q v).coeff n = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v
      by_cases hn0 : n = 0
      · simpa [hn0] using hzero v
      by_cases hn1 : n = 1
      · simpa [hn1] using h v
      obtain ⟨l, hl, hln⟩ := Nat.exists_prime_and_dvd hn1
      have hm : n / l < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) hl.one_lt
      have hmm : n / l / l < n := lt_of_le_of_lt (Nat.div_le_self _ _) hm
      have heq : l * (n / l) = n := Nat.mul_div_cancel' hln
      by_cases hlN : l = N
      · have hh := hU v (n / l)
        rw [← hlN, heq, ih _ hm] at hh
        exact hh
      · have hh := hT l hl hlN v (n / l)
        rw [heq, ih _ hm, ih _ hmm] at hh
        simpa using hh
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  apply hv
  apply hq
  ext n
  simp [hall]

/-- In the same setting, the first-coefficient functional is surjective.
This is the linear-algebra endpoint needed for the cotangent direction at
a cusp, once the geometric expansion map and Hecke formulas are proved. -/
theorem coeff_one_surjective_of_hecke_action
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Nontrivial V]
    (q : V →ₗ[K] PowerSeries K) (hq : Function.Injective q)
    (N : ℕ) (U : V →ₗ[K] V) (T : ℕ → V →ₗ[K] V)
    (hzero : ∀ v, (q v).coeff 0 = 0)
    (hU : ∀ v m, (q v).coeff (N * m) = (q (U v)).coeff m)
    (hT : ∀ l, l.Prime → l ≠ N → ∀ v m,
      (q v).coeff (l * m) = (q (T l v)).coeff m -
        if l ∣ m then (l : K) * (q v).coeff (m / l) else 0) :
    Function.Surjective (fun v ↦ (q v).coeff 1) := by
  obtain ⟨v, hv⟩ := exists_coeff_one_ne_zero_of_hecke_action q hq N U T hzero hU hT
  intro a
  refine ⟨(a / (q v).coeff 1) • v, ?_⟩
  simp [smul_eq_mul, div_mul_cancel₀ _ hv]

end FLT.Mazur
