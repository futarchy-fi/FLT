/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupReesRatioScheme

/-!
# The second chart of a full Rees ratio intersection

Both ratio localizations are compared with one and the same product-generator
homogeneous localization. The second inclusion uses the reversed factors
without changing the underlying target ring or its scheme.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.BlowupRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {A : Type u} [CommRing A] (I : Ideal A) (f : A) (hf : f ∈ I)
  (a : A) (ha : a ∈ I)

/-- The second homogeneous chart maps to the same product-generator localization. -/
def toProductChartRight : DegreeZeroChart I a ha →+* ProductChart I f hf a ha :=
  HomogeneousLocalization.awayMap (component I) (generator_mem I f hf) (mul_comm _ _)

/-- Localizing the second homogeneous chart at f/a gives the same product chart. -/
def rightProductLocalizationEquiv : Localization.Away (degreeOneRatio I a ha f hf) ≃+*
    ProductChart I f hf a ha := by
  let _ := (toProductChartRight I f hf a ha).toAlgebra
  let _ : IsLocalization.Away (degreeOneRatio I a ha f hf)
      (ProductChart I f hf a ha) := by
    rw [← localizationElem_eq_ratio]
    exact HomogeneousLocalization.Away.isLocalization_mul
      (generator_mem I a ha) (generator_mem I f hf) (mul_comm _ _) (by decide)
  exact (IsLocalization.algEquiv (Submonoid.powers (degreeOneRatio I a ha f hf))
    _ (ProductChart I f hf a ha)).toRingEquiv

/-- The second localization comparison extends its actual homogeneous restriction. -/
@[simp] theorem rightProductLocalizationEquiv_base (z : DegreeZeroChart I a ha) :
    rightProductLocalizationEquiv I f hf a ha (homogeneousRatioMap I a ha f hf z) =
      toProductChartRight I f hf a ha z := by
  let _ := (toProductChartRight I f hf a ha).toAlgebra
  let _ : IsLocalization.Away (degreeOneRatio I a ha f hf)
      (ProductChart I f hf a ha) := by
    rw [← localizationElem_eq_ratio]
    exact HomogeneousLocalization.Away.isLocalization_mul
      (generator_mem I a ha) (generator_mem I f hf) (mul_comm _ _) (by decide)
  exact AlgEquiv.commutes (IsLocalization.algEquiv
    (Submonoid.powers (degreeOneRatio I a ha f hf))
    (Localization.Away (degreeOneRatio I a ha f hf)) (ProductChart I f hf a ha)) z

/-- The second full fraction ratio open is the same product-generator chart. -/
def rightFractionRatioEquiv : FractionRatioOpen I a f hf ≃+* ProductChart I f hf a ha :=
  (ratioLocalizationEquiv I a ha f hf).symm.trans
    (rightProductLocalizationEquiv I f hf a ha)

/-- The second comparison retains every fraction-chart function. -/
@[simp] theorem rightFractionRatioEquiv_base (z : BlowupFractionChart.chart I a) :
    rightFractionRatioEquiv I f hf a ha (algebraMap _ _ z) =
      toProductChartRight I f hf a ha ((degreeZeroEquiv I a ha).symm z) := by
  obtain ⟨w, rfl⟩ := (degreeZeroEquiv I a ha).surjective z
  rw [← ratioLocalizationEquiv_base, rightFractionRatioEquiv, RingEquiv.trans_apply,
    RingEquiv.symm_apply_apply, rightProductLocalizationEquiv_base,
    RingEquiv.symm_apply_apply]

/-- The second ratio spectrum is isomorphic to the common product chart. -/
def productRightFractionRatioIso : Spec (.of (ProductChart I f hf a ha)) ≅
    Spec (.of (FractionRatioOpen I a f hf)) :=
  Scheme.Spec.mapIso (rightFractionRatioEquiv I f hf a ha).toCommRingCatIso.op

/-- The second comparison retains its entire homogeneous chart restriction. -/
@[reassoc] theorem productRightFractionRatioIso_base :
    (productRightFractionRatioIso I f hf a ha).hom ≫ fractionRatioInclusion I a f hf ≫
      (fractionSpecIso I a ha).hom =
        Spec.map (CommRingCat.ofHom (toProductChartRight I f hf a ha)) := by
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change rightFractionRatioEquiv I f hf a ha
    (algebraMap _ (FractionRatioOpen I a f hf) (degreeZeroEquiv I a ha z)) = _
  rw [rightFractionRatioEquiv_base, RingEquiv.symm_apply_apply]
  rfl

/-- The second chart inclusion also commutes on the full ratio intersection. -/
@[reassoc] theorem productRightFractionRatioIso_inclusion :
    (productRightFractionRatioIso I f hf a ha).hom ≫ fractionRatioInclusion I a f hf ≫
      fractionChartInclusion I a ha = productChartInclusion I f hf a ha := by
  rw [fractionChartInclusion, productRightFractionRatioIso_base_assoc]
  exact Proj.SpecMap_awayMap_awayι (component I) (generator_mem I a ha)
    (by decide) (generator_mem I f hf) (mul_comm _ _)

end FLT.Mazur.BlowupRees
