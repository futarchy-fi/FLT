/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseBoundaryNumeratorSolutions

/-!
# Exact original correction equations for localized boundary solutions

Starting from any actual boundary lift family, solvability after base
localization is equivalent to an explicit equation in original rings. A single
allowed scalar times its full discrepancy must be the discrepancy of a family
in the exact original boundary kernels. This does not assert that it is.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteBaseLocalizedBoundaryLifts
open FiniteBaseLocalizationDenominators
variable {R : Type*} [CommRing R] (M : Submonoid R)
  {ι : Type*} [Finite ι] {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  (α : ∀ i, R →+* A i)
  (φ : ∀ i, A i →+* B i) (p : ∀ i j, A i →+* C i j) (q : ∀ i j, A j →+* C i j)
  (hα : ∀ i j x, p i j (α i x) = q i j (α j x))
  {S T : ι → Type*} {U : ι → ι → Type*}
  [∀ i, CommRing (S i)] [∀ i, CommRing (T i)] [∀ i j, CommRing (U i j)]
  [∀ i, Algebra (A i) (S i)] [∀ i, Algebra (B i) (T i)]
  [∀ i j, Algebra (C i j) (U i j)]
  [∀ i, IsLocalization (M.map (α i).toMonoidHom) (S i)]
  [∀ i, IsLocalization (M.map ((φ i).comp (α i)).toMonoidHom) (T i)]
  [∀ i j, IsLocalization (M.map ((p i j).comp (α i)).toMonoidHom) (U i j)]
  (β : ∀ i, S i →+* T i) (π : ∀ i j, S i →+* U i j) (ρ : ∀ i j, S j →+* U i j)
  (hβ : ∀ i x, β i (algebraMap _ _ x) = algebraMap _ _ (φ i x))
  (hπ : ∀ i j x, π i j (algebraMap _ _ x) = algebraMap _ _ (p i j x))
  (hρ : ∀ i j x, ρ i j (algebraMap _ _ x) = algebraMap _ _ (q i j x))

include hα hβ hπ hρ in
/-- Localized solvability is exactly an original simultaneous scaled kernel correction. -/
theorem base_localized_iff_scaled_correction (u : ∀ i, A i) (t : ∀ i, B i)
    (hu : ∀ i, φ i (u i) = t i) :
    (∃ v : ∀ i, S i, (∀ i, β i (v i) = algebraMap _ _ (t i)) ∧
      (∀ i j, π i j (v i) = ρ i j (v j))) ↔
    ∃ s : M, ∃ z : ∀ i, A i, (∀ i, φ i (z i) = 0) ∧
      ∀ i j, p i j (z i) - q i j (z j) =
        p i j (α i s) * (p i j (u i) - q i j (u j)) := by
  constructor
  · rintro ⟨v, hb, he⟩
    obtain ⟨s, w, hw, hc⟩ := exists_exact_numerators M α φ p q hα β π ρ hβ hπ hρ v t hb he
    refine ⟨s, fun i ↦ α i s * u i - w i, ?_, ?_⟩
    · intro i
      rw [map_sub, map_mul, hu, hw, sub_self]
    · intro i j
      simp only [map_sub, map_mul, ← hα, hc i j]
      ring
  · rintro ⟨s, z, hz, he⟩
    apply exists_base_localized_of_numerators M α φ p q hα β π ρ hβ hπ hρ s
      (fun i ↦ α i s * u i - z i) t
    · intro i
      rw [map_sub, map_mul, hu, hz, sub_zero]
    · intro i j
      simp only [map_sub, map_mul, ← hα]
      apply sub_eq_zero.mp
      calc
        _ = p i j (α i s) * (p i j (u i) - q i j (u j)) -
            (p i j (z i) - q i j (z j)) := by ring
        _ = 0 := by rw [he, sub_self]

end FLT.Mazur.FiniteBaseLocalizedBoundaryLifts
