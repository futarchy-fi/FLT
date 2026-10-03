/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.PrincipalUnitFiltration
public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Limits of compatible principal congruences

Successive corrections divisible by increasing powers form a Cauchy sequence
for the principal ideal. Adic completeness gives an element with all congruences.
-/

@[expose] public section

namespace LocalClassFieldTheory

variable {R : Type*} [CommRing R]

/-- Successive congruences imply all the pairwise congruences. -/
theorem pow_dvd_sub_of_successive (π : R) (f : ℕ → R)
    (hf : ∀ n, π ^ n ∣ f (n + 1) - f n) {m n : ℕ} (hmn : m ≤ n) :
    π ^ m ∣ f n - f m := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have hstep := (pow_dvd_pow π hmn).trans (hf n)
    convert dvd_add hstep ih using 1
    ring

/-- Divisibility is precisely adic congruence for a principal ideal. -/
theorem principal_smodEq_iff (π : R) (n : ℕ) (x y : R) :
    x ≡ y [SMOD ((Ideal.span {π}) ^ n • ⊤ : Submodule R R)] ↔ π ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/-- Completeness produces a limit preserving every prescribed principal congruence. -/
theorem exists_principal_adic_limit (π : R) [IsPrecomplete (Ideal.span {π}) R]
    (f : ℕ → R) (hf : ∀ n, π ^ n ∣ f (n + 1) - f n) :
    ∃ x : R, ∀ n, π ^ n ∣ f n - x := by
  obtain ⟨x, hx⟩ := IsPrecomplete.prec (I := Ideal.span {π}) (M := R) inferInstance
    (f := f) (fun {m n} hmn => (principal_smodEq_iff π m _ _).2
      (by simpa only [neg_sub] using dvd_neg.mpr (pow_dvd_sub_of_successive π f hf hmn)))
  exact ⟨x, fun n => (principal_smodEq_iff π n _ _).1 (hx n)⟩

/-- Separatedness identifies elements whose differences vanish at every level. -/
theorem eq_of_principal_congruent (π : R) [IsHausdorff (Ideal.span {π}) R]
    (x y : R) (h : ∀ n, π ^ n ∣ x - y) : x = y := by
  rw [IsHausdorff.eq_iff_smodEq (I := Ideal.span {π})]
  exact fun n => (principal_smodEq_iff π n x y).2 (h n)

end LocalClassFieldTheory
