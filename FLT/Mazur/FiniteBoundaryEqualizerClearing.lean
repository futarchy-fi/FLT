/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteLocalizationDenominators

/-!
# Clearing boundary errors and full relation errors simultaneously

Numerators need only have the prescribed boundary value and relation agreement
after localization. Finiteness clears both errors in the original rings, giving
exact scaled boundary values and exact compatibility with one shared numerator
per chart. Boundary kernels and nilpotents are not discarded.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteBoundaryEqualizerClearing
variable {ι : Type*} [Finite ι] {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  (φ : ∀ i, A i →+* B i) (p : ∀ i j, A i →+* C i j) (q : ∀ i j, A j →+* C i j)
  (r : ∀ i, A i) (hr : ∀ i j, p i j (r i) = q i j (r j))
include hr

/-- Power-torsion boundary and relation errors give exact simultaneous scaled lifts. -/
theorem exists_exact_multiple (v : ∀ i, A i) (t : ∀ i, B i) (N : ℕ)
    (hb : ∀ i, ∃ k : ℕ, φ i (r i) ^ k * (φ i (v i) - φ i (r i) ^ N * t i) = 0)
    (he : ∀ i j, ∃ k : ℕ, p i j (r i) ^ k * (p i j (v i) - q i j (v j)) = 0) :
    ∃ M : ℕ, ∃ w : ∀ i, A i,
      (∀ i, φ i (w i) = φ i (r i) ^ M * t i) ∧
      (∀ i j, p i j (w i) = q i j (w j)) := by
  obtain ⟨K, hK⟩ := FinitePowerEqualizer.exists_uniform_power
    (fun i ↦ φ i (r i)) (fun i ↦ φ i (v i) - φ i (r i) ^ N * t i) hb
  obtain ⟨L, hL⟩ := FinitePowerEqualizer.exists_uniform_power
    (fun ij : ι × ι ↦ p ij.1 ij.2 (r ij.1))
    (fun ij ↦ p ij.1 ij.2 (v ij.1) - q ij.1 ij.2 (v ij.2)) (fun ij ↦ he ij.1 ij.2)
  refine ⟨L + K + N, fun i ↦ r i ^ (L + K) * v i, ?_, ?_⟩
  · intro i
    have hi : φ i (r i) ^ K * φ i (v i) = φ i (r i) ^ K * (φ i (r i) ^ N * t i) :=
      sub_eq_zero.mp (by simpa only [mul_sub] using hK i)
    simp only [map_mul, map_pow, pow_add]
    rw [mul_assoc, hi]
    ring
  · intro i j
    have hij : p i j (r i) ^ L * p i j (v i) = p i j (r i) ^ L * q i j (v j) :=
      sub_eq_zero.mp (by simpa only [mul_sub] using hL (i, j))
    simp only [map_mul, map_pow, ← hr i j, pow_add]
    calc
      _ = p i j (r i) ^ K * (p i j (r i) ^ L * p i j (v i)) := by ring
      _ = p i j (r i) ^ K * (p i j (r i) ^ L * q i j (v j)) := by rw [hij]
      _ = _ := by ring

/-- Localized boundary and relation equations construct exact original numerators. -/
theorem exists_exact_of_localized (v : ∀ i, A i) (t : ∀ i, B i) (N : ℕ)
    (hb : ∀ i, algebraMap (B i) (Localization.Away (φ i (r i))) (φ i (v i)) =
      algebraMap (B i) (Localization.Away (φ i (r i))) (φ i (r i) ^ N * t i))
    (he : ∀ i j,
      algebraMap (C i j) (Localization.Away (p i j (r i))) (p i j (v i)) =
      algebraMap (C i j) (Localization.Away (p i j (r i))) (q i j (v j))) :
    ∃ M : ℕ, ∃ w : ∀ i, A i,
      (∀ i, φ i (w i) = φ i (r i) ^ M * t i) ∧
      (∀ i j, p i j (w i) = q i j (w j)) := by
  apply exists_exact_multiple φ p q r hr v t N
  · intro i
    obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq (φ i (r i)) (hb i)
    exact ⟨k, by rw [mul_sub, hk, sub_self]⟩
  · intro i j
    obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq (p i j (r i)) (he i j)
    exact ⟨k, by rw [mul_sub, hk, sub_self]⟩

end FLT.Mazur.FiniteBoundaryEqualizerClearing
