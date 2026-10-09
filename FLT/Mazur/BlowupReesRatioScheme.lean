/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupReesRatioLocalization

/-!
# Scheme compatibility of actual ratio localizations and Rees Proj

The product-generator chart maps to the fraction ratio open, and its
inclusion into Proj commutes with the original fraction chart inclusion.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.BlowupRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {A : Type u} [CommRing A] (I : Ideal A) (f : A) (hf : f ∈ I)
  (a : A) (ha : a ∈ I)

/-- The principal ratio open included in the actual fraction chart. -/
def fractionRatioInclusion : Spec (.of (FractionRatioOpen I f a ha)) ⟶
    Spec (.of (BlowupFractionChart.chart I f)) := Spec.map (CommRingCat.ofHom (algebraMap _ _))

instance fractionRatioInclusion_isOpenImmersion :
    IsOpenImmersion (fractionRatioInclusion I f a ha) :=
  IsOpenImmersion.of_isLocalization (BlowupFractionChart.ratio I f a ha)

/-- The product-generator chart included in the original Rees Proj. -/
def productChartInclusion : Spec (.of (ProductChart I f hf a ha)) ⟶ proj I :=
  Proj.awayι (component I) (generator I f hf * generator I a ha)
    (SetLike.mul_mem_graded (generator_mem I f hf) (generator_mem I a ha)) (by decide)

/-- The product-generator spectrum is the full fraction ratio open. -/
def productFractionRatioIso : Spec (.of (ProductChart I f hf a ha)) ≅
    Spec (.of (FractionRatioOpen I f a ha)) :=
  Scheme.Spec.mapIso (fractionRatioEquiv I f hf a ha).toCommRingCatIso.op

/-- The spectrum comparison retains the full restriction map from the fraction chart. -/
@[reassoc] theorem productFractionRatioIso_base :
    (productFractionRatioIso I f hf a ha).hom ≫ fractionRatioInclusion I f a ha ≫
      (fractionSpecIso I f hf).hom = Spec.map (CommRingCat.ofHom (toProductChart I f hf a ha)) := by
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change fractionRatioEquiv I f hf a ha
    (algebraMap _ (FractionRatioOpen I f a ha) (degreeZeroEquiv I f hf z)) = _
  rw [fractionRatioEquiv_base, RingEquiv.symm_apply_apply]
  rfl

/-- Both actual inclusions into Rees Proj agree on the entire ratio localization. -/
@[reassoc] theorem productFractionRatioIso_inclusion :
    (productFractionRatioIso I f hf a ha).hom ≫ fractionRatioInclusion I f a ha ≫
      fractionChartInclusion I f hf = productChartInclusion I f hf a ha := by
  rw [fractionChartInclusion, productFractionRatioIso_base_assoc]
  exact Proj.SpecMap_awayMap_awayι (component I) (generator_mem I f hf)
    (by decide) (generator_mem I a ha) rfl

/-- The ratio open maps to the product-generator chart with its prescribed inclusion. -/
@[reassoc] theorem productFractionRatioIso_inv_inclusion :
    (productFractionRatioIso I f hf a ha).inv ≫ productChartInclusion I f hf a ha =
      fractionRatioInclusion I f a ha ≫ fractionChartInclusion I f hf := by
  rw [← productFractionRatioIso_inclusion, Iso.inv_hom_id_assoc]

end FLT.Mazur.BlowupRees
