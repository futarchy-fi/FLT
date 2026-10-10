/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupReesRatioOriginal

/-!
# The canonical Rees transition and uniqueness over original functions

The two full ratio opens are isomorphic through the product-generator chart.
Any transition retaining the original coefficient functions equals this one,
so its scheme inclusions into the original Rees Proj commute.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.BlowupRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {A : Type u} [CommRing A] (I : Ideal A) (f : A) (hf : f ∈ I)
  (a : A) (ha : a ∈ I)

/-- The canonical transition between the two actual fraction ratio opens. -/
def ratioTransition : FractionRatioOpen I f a ha ≃+* FractionRatioOpen I a f hf :=
  (fractionRatioEquiv I f hf a ha).trans (rightFractionRatioEquiv I f hf a ha).symm

/-- The canonical transition retains every original function. -/
@[simp] theorem ratioTransition_original (z : A) :
    ratioTransition I f hf a ha (originalOnRatio I f a ha z) =
      originalOnRatio I a f hf z := by
  apply (rightFractionRatioEquiv I f hf a ha).injective
  rw [ratioTransition, RingEquiv.trans_apply, RingEquiv.apply_symm_apply,
    fractionRatioEquiv_original, rightFractionRatioEquiv_original]

/-- Original coordinate functions uniquely determine maps between these ratio opens. -/
theorem ratioTransition_unique (e : FractionRatioOpen I f a ha →+* FractionRatioOpen I a f hf)
    (he : ∀ z, e (originalOnRatio I f a ha z) = originalOnRatio I a f hf z) :
    e = (ratioTransition I f hf a ha).toRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (BlowupFractionChart.ratio I f a ha))
  apply BlowupFractionChart.ringHom_ext_of_denominator_regular I f
    (S := FractionRatioOpen I a f hf) _ _
  · apply RingHom.ext
    intro z
    change e (originalOnRatio I f a ha z) =
      ratioTransition I f hf a ha (originalOnRatio I f a ha z)
    rw [he, ratioTransition_original]
  · change IsRegular (e (originalOnRatio I f a ha f))
    rw [he]
    exact originalOnRatio_numerator_regular I a f hf

/-- The canonical spectrum transition factors through the common product chart. -/
theorem ratioTransition_spec :
    Spec.map (CommRingCat.ofHom (ratioTransition I f hf a ha).toRingHom) =
      (productRightFractionRatioIso I f hf a ha).inv ≫
        (productFractionRatioIso I f hf a ha).hom := by
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- The canonical transition commutes with the actual Rees Proj inclusions. -/
@[reassoc] theorem ratioTransition_inclusion :
    Spec.map (CommRingCat.ofHom (ratioTransition I f hf a ha).toRingHom) ≫
      fractionRatioInclusion I f a ha ≫ fractionChartInclusion I f hf =
        fractionRatioInclusion I a f hf ≫ fractionChartInclusion I a ha := by
  rw [ratioTransition_spec, Category.assoc, productFractionRatioIso_inclusion]
  rw [← productRightFractionRatioIso_inclusion, Iso.inv_hom_id_assoc]

/-- Any proved original-preserving transition commutes on the full Rees intersection. -/
@[reassoc] theorem originalPreservingTransition_inclusion
    (e : FractionRatioOpen I f a ha →+* FractionRatioOpen I a f hf)
    (he : ∀ z, e (originalOnRatio I f a ha z) = originalOnRatio I a f hf z) :
    Spec.map (CommRingCat.ofHom e) ≫
      fractionRatioInclusion I f a ha ≫ fractionChartInclusion I f hf =
        fractionRatioInclusion I a f hf ≫ fractionChartInclusion I a ha := by
  rw [ratioTransition_unique I f hf a ha e he]
  exact ratioTransition_inclusion I f hf a ha

end FLT.Mazur.BlowupRees
