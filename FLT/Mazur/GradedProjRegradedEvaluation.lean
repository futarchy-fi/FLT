/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HomogeneousLocalizationRegradedMap
public import FLT.Mazur.GradedProjUnitChart

/-!
# Evaluation commutes with a change of grading

Evaluation of a homogeneous fraction after applying a regraded ring map is
the original evaluation of its mapped numerator and denominator. This lets
retained section charts reuse the coordinate-independent full-section ratios.
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousLocalization

namespace FLT.Mazur.GradedProjRegradedEvaluation

universe u

variable {A B : Type u} {σ τ : Type*} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  (g : A →+* B) (ρ : ℕ → ℕ) (hg : ∀ d, ∀ a ∈ 𝒜 d, g a ∈ ℬ (ρ d))
  {X : Scheme.{u}} (φ : B →+* Γ(X, ⊤)) (f : A) (hf : IsUnit (φ (g f)))
  (hPQ : Submonoid.powers f ≤ (Submonoid.powers (g f)).comap g)

/-- Regraded localization followed by evaluation is evaluation of the original ring composite. -/
theorem evaluation_comp :
    (GradedProjUnitChart.evaluation ℬ φ (g f) hf).comp
      (HomogeneousLocalizationRegradedMap.map 𝒜 ℬ g ρ hg hPQ) =
        GradedProjUnitChart.evaluation 𝒜 (φ.comp g) f hf := by
  ext z
  obtain ⟨c, rfl⟩ := mk_surjective z
  let e := HomogeneousLocalizationRegradedMap.fraction 𝒜 ℬ g ρ hg hPQ c
  have hu : IsUnit (φ (g c.den)) :=
    GradedProjUnitChart.denominator_isUnit 𝒜 (φ.comp g) f hf c
  apply hu.mul_left_inj.mp
  change GradedProjUnitChart.evaluation ℬ φ (g f) hf
      (HomogeneousLocalizationRegradedMap.map 𝒜 ℬ g ρ hg hPQ (mk c)) * φ (g c.den) =
    GradedProjUnitChart.evaluation 𝒜 (φ.comp g) f hf (mk c) * φ (g c.den)
  rw [HomogeneousLocalizationRegradedMap.map_mk]
  exact (GradedProjUnitChart.evaluation_mk_mul ℬ φ (g f) hf e).trans
    (GradedProjUnitChart.evaluation_mk_mul 𝒜 (φ.comp g) f hf c).symm

end FLT.Mazur.GradedProjRegradedEvaluation
