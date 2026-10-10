/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Homogeneous localization under a change of degrees

A ring homomorphism sending each homogeneous group into a prescribed new
homogeneous group acts on degree-zero fractions. The new degrees need not
exhaust the target grading, as happens for retained section rings.
-/

@[expose] public noncomputable section

open HomogeneousLocalization

namespace FLT.Mazur.HomogeneousLocalizationRegradedMap

variable {A B σ τ : Type*} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  (g : A →+* B) (ρ : ℕ → ℕ) (hg : ∀ d, ∀ a ∈ 𝒜 d, g a ∈ ℬ (ρ d))
  {P : Submonoid A} {Q : Submonoid B} (hPQ : P ≤ Q.comap g)

/-- Apply the original ring map to both homogeneous numerator and denominator. -/
def fraction (c : NumDenSameDeg 𝒜 P) : NumDenSameDeg ℬ Q :=
  ⟨ρ c.deg, ⟨g c.num, hg _ _ c.num.property⟩,
    ⟨g c.den, hg _ _ c.den.property⟩, hPQ c.den_mem⟩

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- The numerator-denominator operation respects equality in ordinary localization. -/
theorem fraction_embedding (c : NumDenSameDeg 𝒜 P) :
    (fraction 𝒜 ℬ g ρ hg hPQ c).embedding =
      IsLocalization.map (Localization Q) g hPQ c.embedding := by
  simp only [fraction, NumDenSameDeg.embedding, Localization.mk_eq_mk',
    IsLocalization.map_mk']

/-- The induced operation on actual homogeneous fractions. -/
def apply (z : HomogeneousLocalization 𝒜 P) : HomogeneousLocalization ℬ Q :=
  Quotient.map' (fraction 𝒜 ℬ g ρ hg hPQ) (fun c e h ↦ by
    change (fraction 𝒜 ℬ g ρ hg hPQ c).embedding =
      (fraction 𝒜 ℬ g ρ hg hPQ e).embedding
    rw [fraction_embedding, fraction_embedding]
    exact congrArg (IsLocalization.map (Localization Q) g hPQ) h) z

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- The regraded operation retains the ordinary localized ring map. -/
theorem apply_val (z : HomogeneousLocalization 𝒜 P) :
    (apply 𝒜 ℬ g ρ hg hPQ z).val =
      IsLocalization.map (Localization Q) g hPQ z.val := by
  obtain ⟨c, rfl⟩ := mk_surjective z
  exact fraction_embedding 𝒜 ℬ g ρ hg hPQ c

/-- Regrading induces a ring homomorphism on homogeneous localizations. -/
def map : HomogeneousLocalization 𝒜 P →+* HomogeneousLocalization ℬ Q where
  toFun := apply 𝒜 ℬ g ρ hg hPQ
  map_one' := by
    apply val_injective
    rw [apply_val, val_one, map_one, val_one]
  map_zero' := by
    apply val_injective
    rw [apply_val, val_zero, map_zero, val_zero]
  map_add' x y := by
    apply val_injective
    rw [apply_val, val_add, map_add, val_add, apply_val, apply_val]
  map_mul' x y := by
    apply val_injective
    rw [apply_val, val_mul, map_mul, val_mul, apply_val, apply_val]

/-- Regrading keeps the original numerator and denominator on every presentation. -/
theorem map_mk (c : NumDenSameDeg 𝒜 P) :
    map 𝒜 ℬ g ρ hg hPQ (mk c) = mk (fraction 𝒜 ℬ g ρ hg hPQ c) := rfl

/-- The ring homomorphism agrees with localization of the original ring map. -/
theorem map_val (z : HomogeneousLocalization 𝒜 P) :
    (map 𝒜 ℬ g ρ hg hPQ z).val =
      IsLocalization.map (Localization Q) g hPQ z.val :=
  apply_val 𝒜 ℬ g ρ hg hPQ z

end FLT.Mazur.HomogeneousLocalizationRegradedMap
