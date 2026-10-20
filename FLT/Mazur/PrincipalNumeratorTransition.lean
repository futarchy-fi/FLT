/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Tactic

/-!
# Matching principal numerators across one transition

Two compatible localized values have global numerators whose transition is
exact after increasing the denominator. The numerators remain in their full
specified ideals. Neither surjectivity of the global transition nor a uniform
bound on the new exponent is assumed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PrincipalNumeratorTransition
variable {R R' S S' : Type*} [CommRing R] [CommRing R'] [CommRing S] [CommRing S']

/-- Raising an exponent preserves a numerator equation. -/
theorem promote (f : R →+* S) (r w : R) (x : S) {m N : ℕ} (hm : m ≤ N)
    (h : f w = f r ^ m * x) : f (r ^ (N - m) * w) = f r ^ N * x := by
  rw [map_mul, map_pow, h, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]

/-- A power annihilating a discrepancy gives an exact, ideal-preserving transition. -/
theorem exists_matching_numerator
    (f : R →+* S) (f' : R' →+* S') (ρ : R' →+* R) (σ : S' →+* S)
    (hsq : ∀ z, f (ρ z) = σ (f' z))
    (r : R) (r' : R') (hr : ρ r' = r) (x : S) (x' : S') (hx : σ x' = x)
    (I' : Ideal R')
    (hdetect : ∀ a b : R, f a = f b → ∃ d : ℕ, r ^ d * a = r ^ d * b)
    (hex : ∃ (m : ℕ) (z : R'), z ∈ I' ∧ f' z = f' r' ^ m * x')
    (N : ℕ) (w : R) (hw : f w = f r ^ N * x) :
    ∃ (M : ℕ) (z : R'), N ≤ M ∧ z ∈ I' ∧ f' z = f' r' ^ M * x' ∧
      ρ z = r ^ (M - N) * w := by
  obtain ⟨m, z, hz, he⟩ := hex
  let L := max N m
  let y := r' ^ (L - m) * z
  have hy : f' y = f' r' ^ L * x' := promote f' r' z x' (le_max_right N m) he
  have heq : f (ρ y) = f (r ^ (L - N) * w) := by
    rw [hsq, hy, map_mul, map_pow, ← hsq, hr, hx]
    exact (promote f r w x (le_max_left N m) hw).symm
  obtain ⟨d, hd⟩ := hdetect _ _ heq
  refine ⟨d + L, r' ^ d * y, by omega, I'.mul_mem_left _ (I'.mul_mem_left _ hz), ?_, ?_⟩
  · rw [map_mul, map_pow, hy, pow_add, mul_assoc]
  · rw [map_mul, map_pow, hr, hd, ← mul_assoc, ← pow_add]
    congr 2
    omega

end FLT.Mazur.PrincipalNumeratorTransition
