/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Clearing denominators in a localized relation equalizer

Localize the source at an invariant function. If the relation restriction
kernel is power torsion at its pullback, every local invariant numerator can
be made globally invariant by a further power. Both relation arrows are retained.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.EqualizerDenominatorClearing
variable {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  (f g : A →+* C) (a : A →+* B) (c : C →+* D) (f' g' : B →+* D)
  (hf : ∀ x, f' (a x) = c (f x)) (hg : ∀ x, g' (a x) = c (g x))
  (s : A) (hs : f s = g s)
  (hzero : ∀ x, c x = 0 → ∃ n : ℕ, f s ^ n * x = 0)
include hf hg hs hzero

/-- Multiplying a local invariant numerator by a further power enforces the whole relation. -/
theorem invariant_numerator (b : B) (hb : f' b = g' b)
    (n : ℕ) (x : A) (hx : b * a s ^ n = a x) :
    ∃ (N : ℕ) (y : A), f y = g y ∧ b * a s ^ N = a y := by
  have hz : c (f x - g x) = 0 := by
    rw [map_sub, ← hf, ← hg, ← hx, map_mul, map_mul, map_pow, map_pow,
      hf s, hg s, hs, hb, sub_self]
  obtain ⟨m, hm⟩ := hzero _ hz
  refine ⟨n + m, s ^ m * x, ?_, ?_⟩
  · rw [map_mul, map_mul, map_pow, map_pow, ← hs]
    exact sub_eq_zero.mp (by simpa only [mul_sub] using hm)
  · rw [map_mul, map_pow, pow_add, ← mul_assoc, hx, mul_comm]

include hf hg hs hzero in
/-- Source localization and relation power torsion give an actual invariant numerator. -/
theorem exists_invariant_numerator
    (hloc : @IsLocalization.Away _ _ s B _ a.toAlgebra)
    (b : B) (hb : f' b = g' b) :
    ∃ (N : ℕ) (y : A), f y = g y ∧ b * a s ^ N = a y := by
  let _ := a.toAlgebra
  let _ : IsLocalization.Away s B := hloc
  obtain ⟨n, x, hx⟩ := IsLocalization.Away.surj s b
  exact invariant_numerator f g a c f' g' hf hg s hs hzero b hb n x hx

end FLT.Mazur.EqualizerDenominatorClearing
