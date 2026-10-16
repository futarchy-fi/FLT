/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteLocalizedBoundaryMapLifts

/-!
# Principal localized solutions constructed from exact numerators

Divide compatible original numerators by their common scalar power. Unit
cancellation proves the localized boundary and FULL mixed equations without
assuming localization is injective. This is the converse to denominator clearing.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteLocalizedBoundaryLifts
variable {ι : Type*} {A B : ι → Type*} {C : ι → ι → Type*}
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

/-- Exact scaled compatible numerators construct genuine principal localized solutions. -/
theorem exists_localized_of_numerators (w : ∀ i, A i) (t : ∀ i, B i) (N : ℕ)
    (hb : ∀ i, φ i (w i) = φ i (r i) ^ N * t i)
    (he : ∀ i j, p i j (w i) = q i j (w j)) :
    ∃ v : ∀ i, Localization.Away (r i),
      (∀ i, β i (v i) = algebraMap _ _ (t i)) ∧
      (∀ i j, π i j (v i) = ρ i j (v j)) := by
  let v (i : ι) : Localization.Away (r i) :=
    IsLocalization.Away.invSelf (r i) ^ N * algebraMap _ _ (w i)
  have hv (i : ι) : algebraMap _ (Localization.Away (r i)) (r i) ^ N * v i =
      algebraMap _ _ (w i) := by
    dsimp only [v]
    rw [← mul_assoc, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, one_mul]
  refine ⟨v, ?_, ?_⟩
  · intro i
    apply ((IsLocalization.Away.algebraMap_isUnit (φ i (r i))).pow N).mul_right_inj.mp
    calc
      _ = β i (algebraMap _ _ (r i) ^ N * v i) := by simp only [map_mul, map_pow, hβ]
      _ = algebraMap _ _ (φ i (w i)) := by rw [hv, hβ]
      _ = _ := by rw [hb, map_mul, map_pow]
  · intro i j
    apply ((IsLocalization.Away.algebraMap_isUnit (p i j (r i))).pow N).mul_right_inj.mp
    calc
      _ = π i j (algebraMap _ _ (r i) ^ N * v i) := by simp only [map_mul, map_pow, hπ]
      _ = algebraMap _ _ (p i j (w i)) := by rw [hv, hπ]
      _ = algebraMap _ _ (q i j (w j)) := by rw [he]
      _ = ρ i j (algebraMap _ _ (r j) ^ N * v j) := by rw [hv, hρ]
      _ = _ := by simp only [map_mul, map_pow, hρ, ← hr]

end FLT.Mazur.FiniteLocalizedBoundaryLifts
