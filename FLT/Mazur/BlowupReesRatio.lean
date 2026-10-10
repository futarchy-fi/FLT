/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupReesProjChart
public import FLT.Mazur.BlowupFractionChartRatio

/-!
# Original ratios on the actual Rees Proj charts

The homogeneous fraction (a*T)/(f*T) is the original fraction a/f.
Consequently chart intersections are the full ratio opens, including their
exceptional points; no original denominator is inverted in this comparison.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.BlowupRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {A : Type u} [CommRing A] (I : Ideal A) (f : A) (hf : f ∈ I)
  (a : A) (ha : a ∈ I)

/-- The homogeneous degree-one ratio in the actual Rees localization. -/
def degreeOneRatio : DegreeZeroChart I f hf :=
  homogeneousFraction I f hf 1 ⟨a, by simpa only [pow_one] using ha⟩

/-- The degree-zero comparison sends the original homogeneous ratio to a/f. -/
@[simp] theorem degreeZeroEquiv_ratio :
    degreeZeroEquiv I f hf (degreeOneRatio I f hf a ha) =
      BlowupFractionChart.ratio I f a ha := by
  apply Subtype.ext
  rw [degreeOneRatio, degreeZeroEquiv_fraction]
  simp only [pow_one, BlowupFractionChart.ratio_val]

/-- The Proj intersection element is precisely the degree-one homogeneous ratio. -/
theorem localizationElem_eq_ratio :
    HomogeneousLocalization.Away.isLocalizationElem (generator_mem I f hf)
      (generator_mem I a ha) = degreeOneRatio I f hf a ha := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.isLocalizationElem,
    HomogeneousLocalization.Away.val_mk, degreeOneRatio, homogeneousFraction, pow_one]
  rfl

set_option backward.isDefEq.respectTransparency true in
/-- The spectrum comparison retains the principal open of the original ratio. -/
theorem fractionSpecIso_preimage_ratio :
    (fractionSpecIso I f hf).hom ⁻¹ᵁ
      PrimeSpectrum.basicOpen (degreeOneRatio I f hf a ha) =
        PrimeSpectrum.basicOpen (BlowupFractionChart.ratio I f a ha) := by
  ext x
  change degreeZeroEquiv I f hf (degreeOneRatio I f hf a ha) ∉ x.asIdeal ↔
    BlowupFractionChart.ratio I f a ha ∉ x.asIdeal
  rw [degreeZeroEquiv_ratio]

/-- The inverse image of another original generator open is the actual ratio open. -/
theorem fractionChartInclusion_preimage :
    fractionChartInclusion I f hf ⁻¹ᵁ generatorOpen I a ha =
      PrimeSpectrum.basicOpen (BlowupFractionChart.ratio I f a ha) := by
  have h := Proj.awayι_preimage_basicOpen (component I)
    (generator_mem I f hf) (by decide : 0 < 1)
    (generator_mem I a ha) (by decide : 0 < 1)
  rw [localizationElem_eq_ratio] at h
  exact (congrArg (fun U => (fractionSpecIso I f hf).hom ⁻¹ᵁ U) h).trans
    (fractionSpecIso_preimage_ratio I f hf a ha)

end FLT.Mazur.BlowupRees
