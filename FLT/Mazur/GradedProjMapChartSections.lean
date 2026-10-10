/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Sheaf evaluation with a specified image denominator

The graded Proj map evaluates fractions in a chosen target denominator.
An equality with the actual image is enough; no chart is replaced abstractly.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

namespace FLT.Mazur.GradedProjMapChartSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] Proj.map

variable {A B : Type} [CommRing A] [CommRing B]
  {σ τ : Type} [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  (φ : 𝒜 →+*ᵍ ℬ) (s : A) (t : B) (ht : φ s = t)

include ht in
omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- The original graded map carries powers of the chosen denominator to its specified image. -/
theorem powers_le : Submonoid.powers s ≤ (Submonoid.powers t).comap φ := by
  rintro _ ⟨k, rfl⟩
  exact ⟨k, (map_pow φ s k).trans (congrArg (· ^ k) ht) |>.symm⟩

/-- The original homogeneous fraction map with the explicitly specified target denominator. -/
def fractionMap : Away 𝒜 s →+* Away ℬ t :=
  HomogeneousLocalization.map φ (powers_le 𝒜 ℬ φ s t ht)

/-- The actual Proj structure-sheaf map retains this chosen denominator. -/
theorem awayToSection_appLE (hφ : HomogeneousIdeal.irrelevant ℬ ≤
    (HomogeneousIdeal.irrelevant 𝒜).map φ) {d : ℕ} (hs : s ∈ 𝒜 d) :
    Proj.awayToSection 𝒜 s ≫ Scheme.Hom.appLE
        (Proj.map (A := A) (B := B) (𝒜 := 𝒜) (ℬ := ℬ) φ hφ)
        (Proj.basicOpen 𝒜 s) (Proj.basicOpen ℬ t)
        (by rw [Proj.map_preimage_basicOpen, ht]) =
      CommRingCat.ofHom (fractionMap 𝒜 ℬ φ s t ht) ≫ Proj.awayToSection ℬ t := by
  subst t
  exact Proj.awayToSection_comp_appLE φ hφ hs

/-- Numerator and denominator are the actual specified image elements. -/
theorem fractionMap_ratio {d : ℕ} (hs : s ∈ 𝒜 d) (ht' : t ∈ ℬ d)
    (a : A) (ha : a ∈ 𝒜 d) (b : B) (hb : b ∈ ℬ d) (hab : φ a = b) :
    fractionMap 𝒜 ℬ φ s t ht
        (Away.mk 𝒜 hs 1 a (by simpa only [one_smul] using ha)) =
      Away.mk ℬ ht' 1 b (by simpa only [one_smul] using hb) := by
  subst t
  subst b
  exact Away.map_mk φ s hs 1 a (by simpa only [one_smul] using ha)

end FLT.Mazur.GradedProjMapChartSections
