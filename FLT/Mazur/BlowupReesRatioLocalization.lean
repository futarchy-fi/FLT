/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupReesRatio

/-!
# The full ratio localization is the product-generator Rees chart

Localizing A[I/f] at a/f gives the degree-zero localization of the actual
Rees algebra at (f*T)(a*T). The comparison retains the map from the f-chart.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.BlowupRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {A : Type u} [CommRing A] (I : Ideal A) (f : A) (hf : f ∈ I)
  (a : A) (ha : a ∈ I)

/-- The actual ratio localization, without inverting the original denominator. -/
abbrev FractionRatioOpen := Localization.Away (BlowupFractionChart.ratio I f a ha)

/-- The actual homogeneous localization at the product of two degree-one generators. -/
abbrev ProductChart := HomogeneousLocalization.Away (component I)
  (generator I f hf * generator I a ha)

/-- The f-chart maps to the actual product-generator homogeneous localization. -/
def toProductChart : DegreeZeroChart I f hf →+* ProductChart I f hf a ha :=
  HomogeneousLocalization.awayMap (component I) (generator_mem I a ha) rfl

/-- The canonical map into the homogeneous ratio localization. -/
def homogeneousRatioMap : DegreeZeroChart I f hf →+*
    Localization.Away (degreeOneRatio I f hf a ha) := algebraMap _ _

/-- Transport the ratio localization through the actual degree-zero comparison. -/
def ratioLocalizationEquiv : Localization.Away (degreeOneRatio I f hf a ha) ≃+*
    FractionRatioOpen I f a ha :=
  IsLocalization.ringEquivOfRingEquiv
    (Localization.Away (degreeOneRatio I f hf a ha)) (FractionRatioOpen I f a ha)
    (M := Submonoid.powers (degreeOneRatio I f hf a ha))
    (T := Submonoid.powers (BlowupFractionChart.ratio I f a ha))
    (degreeZeroEquiv I f hf) (by
    rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers (degreeZeroEquiv_ratio I f hf a ha))

/-- The transported localization map retains every degree-zero chart function. -/
@[simp] theorem ratioLocalizationEquiv_base (z : DegreeZeroChart I f hf) :
    ratioLocalizationEquiv I f hf a ha (homogeneousRatioMap I f hf a ha z) =
      algebraMap _ (FractionRatioOpen I f a ha) (degreeZeroEquiv I f hf z) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ _

/-- The product-generator chart is the localization at the homogeneous ratio. -/
def productLocalizationEquiv : Localization.Away (degreeOneRatio I f hf a ha) ≃+*
    ProductChart I f hf a ha := by
  let _ := (toProductChart I f hf a ha).toAlgebra
  let _ : IsLocalization.Away (degreeOneRatio I f hf a ha)
      (ProductChart I f hf a ha) := by
    rw [← localizationElem_eq_ratio]
    exact HomogeneousLocalization.Away.isLocalization_mul
      (generator_mem I f hf) (generator_mem I a ha) rfl (by decide)
  exact (IsLocalization.algEquiv (Submonoid.powers (degreeOneRatio I f hf a ha))
    _ (ProductChart I f hf a ha)).toRingEquiv

/-- The product comparison extends the actual homogeneous restriction map. -/
@[simp] theorem productLocalizationEquiv_base (z : DegreeZeroChart I f hf) :
    productLocalizationEquiv I f hf a ha (homogeneousRatioMap I f hf a ha z) =
      toProductChart I f hf a ha z := by
  let _ := (toProductChart I f hf a ha).toAlgebra
  let _ : IsLocalization.Away (degreeOneRatio I f hf a ha)
      (ProductChart I f hf a ha) := by
    rw [← localizationElem_eq_ratio]
    exact HomogeneousLocalization.Away.isLocalization_mul
      (generator_mem I f hf) (generator_mem I a ha) rfl (by decide)
  exact AlgEquiv.commutes (IsLocalization.algEquiv
    (Submonoid.powers (degreeOneRatio I f hf a ha))
    (Localization.Away (degreeOneRatio I f hf a ha)) (ProductChart I f hf a ha)) z

/-- The full fraction ratio open is the actual product-generator Proj chart. -/
def fractionRatioEquiv : FractionRatioOpen I f a ha ≃+* ProductChart I f hf a ha :=
  (ratioLocalizationEquiv I f hf a ha).symm.trans (productLocalizationEquiv I f hf a ha)

/-- The fraction ratio comparison retains the entire original chart restriction. -/
@[simp] theorem fractionRatioEquiv_base (z : BlowupFractionChart.chart I f) :
    fractionRatioEquiv I f hf a ha (algebraMap _ _ z) =
      toProductChart I f hf a ha ((degreeZeroEquiv I f hf).symm z) := by
  obtain ⟨w, rfl⟩ := (degreeZeroEquiv I f hf).surjective z
  rw [← ratioLocalizationEquiv_base, fractionRatioEquiv, RingEquiv.trans_apply,
    RingEquiv.symm_apply_apply, productLocalizationEquiv_base, RingEquiv.symm_apply_apply]

end FLT.Mazur.BlowupRees
