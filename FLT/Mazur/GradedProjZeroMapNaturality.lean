/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Naturality for specified degree-zero coefficient maps

The coefficient maps may be arbitrary ring maps into the degree-zero rings.
This avoids changing the original graded rings' scalar structures.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization

universe u

namespace FLT.Mazur.GradedProjZeroMapNaturality

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {A B R σ τ : Type u} [CommRing A] [CommRing B] [CommRing R]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  (f : 𝒜 →+*ᵍ ℬ) (α : R →+* 𝒜 0) (β : R →+* ℬ 0)
  (h : ∀ r, f (α r).val = (β r).val)

include h

/-- Localization preserves the specified original degree-zero coefficients. -/
theorem away_map_zero (s : A) (r : R) :
    Away.map f s (fromZeroRingHom 𝒜 _ (α r)) =
      fromZeroRingHom ℬ _ (β r) := by
  apply HomogeneousLocalization.val_injective
  change Localization.mk (f (α r).val) ⟨f 1, _⟩ =
    Localization.mk (β r).val ⟨1, _⟩
  simp only [h, map_one]

/-- A graded map preserving specified coefficients preserves their structural spectrum map. -/
@[reassoc]
theorem map_toSpec (hf : ℬ₊ ≤ 𝒜₊.map f) :
    Proj.map f hf ≫ Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom α) =
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom β) := by
  apply (Proj.mapAffineOpenCover f hf).openCover.hom_ext
  intro s
  change Proj.awayι _ _ _ _ ≫ _ = Proj.awayι _ _ _ _ ≫ _
  rw [← Category.assoc, Proj.awayι_comp_map f hf s.1.2 s.2 s.2.2,
    Category.assoc, Proj.awayι_toSpecZero_assoc, Proj.awayι_toSpecZero_assoc]
  simp only [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact away_map_zero 𝒜 ℬ f α β h s.2 r

end FLT.Mazur.GradedProjZeroMapNaturality
