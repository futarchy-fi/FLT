/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjLineCoordinates

/-!
# Basic opens of equal-degree homogeneous fractions

The original ratio has the same nonvanishing locus as its numerator chart.
This retains the coordinate itself, even when the common degree exceeds one.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

namespace FLT.Mazur.GradedProjLine

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {ι : Type} (f : ι → A)
  {d : ℕ} (hf : ∀ i, f i ∈ 𝒜 d)

/-- The localization element is the common-degree power of the original fraction. -/
theorem localizationElem_eq_coordinate_pow (i j : ι) :
    Away.isLocalizationElem (hf i) (hf j) = coordinate 𝒜 f hf i j ^ d := by
  apply val_injective
  simp only [Away.isLocalizationElem, coordinate, val_pow, Away.val_mk,
    Localization.mk_pow, pow_one]
  rfl

/-- On the affine homogeneous chart, the fraction cuts out the numerator chart. -/
theorem away_preimage_chart (hd : 0 < d) (i j : ι) :
    Proj.awayι 𝒜 (f i) (hf i) hd ⁻¹ᵁ chart 𝒜 f j =
      PrimeSpectrum.basicOpen (coordinate 𝒜 f hf i j) := by
  change Proj.awayι 𝒜 (f i) (hf i) hd ⁻¹ᵁ Proj.basicOpen 𝒜 (f j) = _
  erw [Proj.awayι_preimage_basicOpen (𝒜 := 𝒜) (hf i) hd (hf j) hd,
    localizationElem_eq_coordinate_pow, PrimeSpectrum.basicOpen_pow _ _ hd]

/-- The inverse chart isomorphism recovers the original homogeneous fraction. -/
theorem awaySection_iso_inv (hd : 0 < d) (i : ι) :
    Proj.awayToSection 𝒜 (f i) ≫ (chart 𝒜 f i).topIso.inv ≫
        (Proj.basicOpenIsoSpec 𝒜 (f i) (hf i) hd).inv.appTop =
      (Scheme.ΓSpecIso (.of (Away 𝒜 (f i)))).inv := by
  have h := Proj.basicOpenToSpec_app_top 𝒜 (f i)
  change (Proj.basicOpenIsoSpec 𝒜 (f i) (hf i) hd).hom.appTop = _ at h
  rw [← Iso.inv_comp_eq] at h
  dsimp only [chart]
  rw [← Category.assoc, ← h]
  simp [← Scheme.Hom.comp_appTop]

/-- The ratio section on the original open subscheme detects the numerator chart. -/
theorem coordinateSection_basicOpen (hd : 0 < d) (i j : ι) :
    (chart 𝒜 f i).toScheme.basicOpen
        ((chart 𝒜 f i).topIso.inv
          (Proj.awayToSection 𝒜 (f i) (coordinate 𝒜 f hf i j))) =
      (chart 𝒜 f i).ι ⁻¹ᵁ chart 𝒜 f j := by
  let e := Proj.basicOpenIsoSpec 𝒜 (f i) (hf i) hd
  suffices h : e.inv ⁻¹ᵁ _ = e.inv ⁻¹ᵁ _ by
    have hh := congrArg (fun U ↦ e.hom ⁻¹ᵁ U) h
    simpa only [← Scheme.Hom.comp_preimage, Iso.hom_inv_id,
      Scheme.Hom.id_preimage] using hh
  dsimp only [chart] at *
  erw [Scheme.Hom.preimage_basicOpen_top, ← Scheme.Hom.comp_preimage]
  have h := ConcreteCategory.congr_hom (awaySection_iso_inv 𝒜 f hf hd i)
    (coordinate 𝒜 f hf i j)
  change e.inv.appTop ((chart 𝒜 f i).topIso.inv
    (Proj.awayToSection 𝒜 (f i) (coordinate 𝒜 f hf i j))) = _ at h
  dsimp only [chart] at h
  rw [h, basicOpen_eq_of_affine]
  exact (away_preimage_chart 𝒜 f hf hd i j).symm

end FLT.Mazur.GradedProjLine
