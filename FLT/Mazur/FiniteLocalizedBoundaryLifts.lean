/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteBoundaryEqualizerClearing

/-!
# Constructing simultaneous original lifts from localized chart solutions

Localized solutions may have different denominators and only localized boundary
agreement. Clearing these denominators and both kinds of error produces one
family of original numerators satisfying every full relation equation exactly.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PrincipalLocalizationMap
variable {A B : Type*} [CommRing A] [CommRing B]

/-- The actual localization map, allowing equal rather than definitionally equal scalars. -/
def map (φ : A →+* B) (r : A) (s : B) (h : φ r = s) :
    Localization.Away r →+* Localization.Away s :=
  IsLocalization.Away.lift r (g := (algebraMap B (Localization.Away s)).comp φ) (by
    change IsUnit (algebraMap B (Localization.Away s) (φ r))
    rw [h]
    exact IsLocalization.Away.algebraMap_isUnit s)

/-- Localized pullback retains the unchanged original coefficient map. -/
theorem map_algebraMap (φ : A →+* B) (r : A) (s : B) (h : φ r = s) (a : A) :
    map φ r s h (algebraMap A (Localization.Away r) a) =
      algebraMap B (Localization.Away s) (φ a) :=
  IsLocalization.Away.lift_eq _ _ _

end FLT.Mazur.PrincipalLocalizationMap

namespace FLT.Mazur.FiniteLocalizedBoundaryLifts
open PrincipalLocalizationMap
variable {ι : Type*} [Finite ι] {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  (φ : ∀ i, A i →+* B i) (p : ∀ i j, A i →+* C i j) (q : ∀ i j, A j →+* C i j)
  (r : ∀ i, A i) (hr : ∀ i j, p i j (r i) = q i j (r j))

/-- Localized compatible chart solutions give exact power-scaled original boundary lifts. -/
theorem exists_original_numerators (v : ∀ i, Localization.Away (r i)) (t : ∀ i, B i)
    (hb : ∀ i, map (φ i) (r i) (φ i (r i)) rfl (v i) =
      algebraMap (B i) (Localization.Away (φ i (r i))) (t i))
    (he : ∀ i j, map (p i j) (r i) (p i j (r i)) rfl (v i) =
      map (q i j) (r j) (p i j (r i)) (hr i j).symm (v j)) :
    ∃ N : ℕ, ∃ w : ∀ i, A i,
      (∀ i, φ i (w i) = φ i (r i) ^ N * t i) ∧
      (∀ i j, p i j (w i) = q i j (w j)) := by
  obtain ⟨N, a, ha⟩ := FiniteLocalizationDenominators.exists_numerators r v
  apply FiniteBoundaryEqualizerClearing.exists_exact_of_localized φ p q r hr a t N
  · intro i
    rw [← map_algebraMap (φ i) (r i) (φ i (r i)) rfl, ha i]
    rw [map_mul, map_pow, map_algebraMap, hb i, map_mul, map_pow]
  · intro i j
    rw [← map_algebraMap (p i j) (r i) (p i j (r i)) rfl,
      ← map_algebraMap (q i j) (r j) (p i j (r i)) (hr i j).symm, ha i, ha j]
    simp only [map_mul, map_pow, map_algebraMap, ← hr i j, he i j]

end FLT.Mazur.FiniteLocalizedBoundaryLifts
