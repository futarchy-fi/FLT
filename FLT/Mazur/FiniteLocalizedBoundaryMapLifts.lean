/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteLocalizedBoundaryLifts

/-!
# Clearing localized lifts through specified coefficient maps

The localized maps enter through their original-coefficient naturality equations.
This keeps the construction independent of their implementation and avoids
unfolding geometric localization maps when specializing to actual chart rings.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteLocalizedBoundaryLifts
variable {ι : Type*} [Finite ι] {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  (φ : ∀ i, A i →+* B i) (p : ∀ i j, A i →+* C i j) (q : ∀ i j, A j →+* C i j)
  (r : ∀ i, A i) (hr : ∀ i j, p i j (r i) = q i j (r j))
  (β : ∀ i, Localization.Away (r i) →+* Localization.Away (φ i (r i)))
  (π : ∀ i j, Localization.Away (r i) →+* Localization.Away (p i j (r i)))
  (ρ : ∀ i j, Localization.Away (r j) →+* Localization.Away (p i j (r i)))
  (hβ : ∀ i x, β i (algebraMap _ _ x) = algebraMap _ _ (φ i x))
  (hπ : ∀ i j x, π i j (algebraMap _ _ x) = algebraMap _ _ (p i j x))
  (hρ : ∀ i j x, ρ i j (algebraMap _ _ x) = algebraMap _ _ (q i j x))

include hr hβ hπ hρ

/-- Naturality suffices to clear all boundary and full mixed equations simultaneously. -/
theorem exists_numerators_of_maps (v : ∀ i, Localization.Away (r i)) (t : ∀ i, B i)
    (hb : ∀ i, β i (v i) = algebraMap _ _ (t i))
    (he : ∀ i j, π i j (v i) = ρ i j (v j)) :
    ∃ N : ℕ, ∃ w : ∀ i, A i,
      (∀ i, φ i (w i) = φ i (r i) ^ N * t i) ∧
      (∀ i j, p i j (w i) = q i j (w j)) := by
  obtain ⟨N, a, ha⟩ := FiniteLocalizationDenominators.exists_numerators r v
  apply FiniteBoundaryEqualizerClearing.exists_exact_of_localized φ p q r hr a t N
  · intro i
    rw [← hβ i, ha i, map_mul, map_pow, hβ, hb i, map_mul, map_pow]
  · intro i j
    rw [← hπ i j, ← hρ i j, ha i, ha j]
    simp only [map_mul, map_pow, hπ, hρ, ← hr i j, he i j]

end FLT.Mazur.FiniteLocalizedBoundaryLifts
