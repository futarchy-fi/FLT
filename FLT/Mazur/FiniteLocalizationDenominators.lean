/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePowerEqualizer
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Common denominators for finite families of principal localizations

One exponent represents all localized chart sections by original numerators.
Another exponent clears finitely many localized equalities in the original
rings, without assuming that localization is injective.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteLocalizationDenominators
variable {ι : Type*} [Finite ι] {A S : ι → Type*}
  [∀ j, CommRing (A j)] [∀ j, CommRing (S j)] [∀ j, Algebra (A j) (S j)]
  (r : ∀ j, A j) [∀ j, IsLocalization.Away (r j) (S j)]

/-- A finite family of fractions has actual numerators with one common power denominator. -/
theorem exists_numerators (v : ∀ j, S j) :
    ∃ N : ℕ, ∃ a : ∀ j, A j, ∀ j,
      algebraMap (A j) (S j) (a j) = algebraMap (A j) (S j) (r j) ^ N * v j := by
  classical
  let _ := Fintype.ofFinite ι
  choose n a ha using fun j ↦ IsLocalization.Away.surj (r j) (v j)
  let N := Finset.univ.sup n
  have hn (j : ι) : n j ≤ N := Finset.le_sup (f := n) (Finset.mem_univ j)
  refine ⟨N, fun j ↦ r j ^ (N - n j) * a j, fun j ↦ ?_⟩
  rw [map_mul, map_pow, ← ha j]
  calc
    _ = (algebraMap (A j) (S j) (r j) ^ (N - n j) *
        algebraMap (A j) (S j) (r j) ^ n j) * v j := by ring
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel (hn j)]

/-- Finitely many localized equalities hold in the original rings after one power multiple. -/
theorem exists_power_equalities (a b : ∀ j, A j)
    (h : ∀ j, algebraMap (A j) (S j) (a j) = algebraMap (A j) (S j) (b j)) :
    ∃ N : ℕ, ∀ j, r j ^ N * a j = r j ^ N * b j := by
  have he (j : ι) : ∃ N : ℕ, r j ^ N * (a j - b j) = 0 := by
    obtain ⟨N, hN⟩ := IsLocalization.Away.exists_of_eq (r j) (h j)
    exact ⟨N, by rw [mul_sub, hN, sub_self]⟩
  obtain ⟨N, hN⟩ := FinitePowerEqualizer.exists_uniform_power r (fun j ↦ a j - b j) he
  exact ⟨N, fun j ↦ sub_eq_zero.mp (by simpa only [mul_sub] using hN j)⟩

end FLT.Mazur.FiniteLocalizationDenominators
