/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinitySmoothChart
public import FLT.Mazur.WeierstrassSmoothProductOpen

/-!
# The smooth infinity domain inside the Y-chart product

The smooth-input restriction of the original infinity neighborhood is an open
subscheme of the smooth Y/Y product, with the original domain inclusion.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The left input of the infinity domain is its original product projection. -/
theorem infinityAdditionInclusion_left :
    infinityAdditionInclusion W ≫
        Spec.map (CommRingCat.ofHom (chartProductLeft W 1 1).toRingHom) =
      Spec.map (CommRingCat.ofHom (infinityInputLeft W).toRingHom) := by
  rw [infinityAdditionInclusion, ← Spec.map_comp]
  rfl

/-- The right input of the infinity domain is its original product projection. -/
theorem infinityAdditionInclusion_right :
    infinityAdditionInclusion W ≫
        Spec.map (CommRingCat.ofHom (chartProductRight W 1 1).toRingHom) =
      Spec.map (CommRingCat.ofHom (infinityInputRight W).toRingHom) := by
  rw [infinityAdditionInclusion, ← Spec.map_comp]
  rfl

/-- The infinity smooth-input open is the restriction from the original product chart. -/
theorem infinitySmoothInputOpen_preimage :
    infinityAdditionInclusion W ⁻¹ᵁ
        smoothProductChartOpen W true true =
      infinitySmoothInputOpen W := by
  have he : smoothProductChartOpen W true true =
      Spec.map (CommRingCat.ofHom (chartProductLeft W 1 1).toRingHom) ⁻¹ᵁ
        (chartStructure W 1).smoothLocus ⊓
      Spec.map (CommRingCat.ofHom (chartProductRight W 1 1).toRingHom) ⁻¹ᵁ
        (chartStructure W 1).smoothLocus := smoothProductChartOpen_eq W true true
  rw [he, Scheme.Hom.preimage_inf, infinitySmoothInputOpen]
  simp only [Scheme.Hom.comp_preimage, integralCurveChart_preimage_smooth]
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
    infinityAdditionInclusion_left, infinityAdditionInclusion_right]

/-- The original input map of the smooth infinity domain. -/
def smoothInfinityInput :
    (infinitySmoothInputOpen W).toScheme ⟶
        Spec (.of (ChartProduct W 1 1)) :=
  (infinitySmoothInputOpen W).ι ≫
    infinityAdditionInclusion W

/-- The smooth infinity domain is open in the original input chart. -/
instance smoothInfinityInput_isOpenImmersion :
    IsOpenImmersion (smoothInfinityInput W) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The original infinity domain restricted inside the smooth input chart product. -/
def smoothInfinityToInputs :
    (infinitySmoothInputOpen W).toScheme ⟶ (smoothProductChartOpen W true true).toScheme :=
  IsOpenImmersion.lift (smoothProductChartOpen W true true).ι (smoothInfinityInput W) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    exact (infinitySmoothInputOpen_preimage W).ge p.property)

/-- The restricted infinity input morphism preserves the original product inclusion. -/
@[reassoc] theorem smoothInfinityToInputs_inclusion :
    smoothInfinityToInputs W ≫ (smoothProductChartOpen W true true).ι =
      smoothInfinityInput W :=
  IsOpenImmersion.lift_fac _ _ _

/-- The infinity smooth domain remains an open immersion after restriction. -/
instance smoothInfinityToInputs_isOpenImmersion :
    IsOpenImmersion (smoothInfinityToInputs W) :=
  inferInstanceAs (IsOpenImmersion (IsOpenImmersion.lift _ _ _))

end FLT.Mazur.WeierstrassIntegralChart
