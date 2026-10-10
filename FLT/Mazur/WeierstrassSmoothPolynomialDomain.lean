/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassPolynomialSmoothChart
public import FLT.Mazur.WeierstrassSmoothProductOpen

/-!
# Smooth polynomial domains inside the projective input charts

The polynomial smooth-input condition is exactly the inverse image of the
smooth input-chart open. Thus every original polynomial domain restricts to
an actual open subscheme of that smooth input product.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The left input of a polynomial domain is its original product projection. -/
theorem projectiveAdditionInclusion_left (j k t : Fin 3) :
    projectiveAdditionInclusion W j k t ≫
        Spec.map (CommRingCat.ofHom (chartProductLeft W j k).toRingHom) =
      Spec.map (CommRingCat.ofHom (polynomialInputLeft W j k t).toRingHom) := by
  rw [projectiveAdditionInclusion, ← Spec.map_comp]
  rfl

/-- The right input of a polynomial domain is its original product projection. -/
theorem projectiveAdditionInclusion_right (j k t : Fin 3) :
    projectiveAdditionInclusion W j k t ≫
        Spec.map (CommRingCat.ofHom (chartProductRight W j k).toRingHom) =
      Spec.map (CommRingCat.ofHom (polynomialInputRight W j k t).toRingHom) := by
  rw [projectiveAdditionInclusion, ← Spec.map_comp]
  rfl

/-- The polynomial smooth-input open is the restriction from the original product chart. -/
theorem polynomialSmoothInputOpen_preimage (b c : Bool) (t : Fin 3) :
    projectiveAdditionInclusion W (productChartCoordinate b) (productChartCoordinate c) t ⁻¹ᵁ
        smoothProductChartOpen W b c =
      polynomialSmoothInputOpen W (productChartCoordinate b) (productChartCoordinate c) t := by
  rw [smoothProductChartOpen_eq, Scheme.Hom.preimage_inf, polynomialSmoothInputOpen]
  simp only [Scheme.Hom.comp_preimage, integralCurveChart_preimage_smooth]
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
    projectiveAdditionInclusion_left, projectiveAdditionInclusion_right]

/-- The original input map of the smooth polynomial domain. -/
def smoothPolynomialInput (b c : Bool) (t : Fin 3) :
    (polynomialSmoothInputOpen W (productChartCoordinate b) (productChartCoordinate c)
      t).toScheme ⟶
        Spec (.of (ChartProduct W (productChartCoordinate b) (productChartCoordinate c))) :=
  (polynomialSmoothInputOpen W (productChartCoordinate b) (productChartCoordinate c) t).ι ≫
    projectiveAdditionInclusion W (productChartCoordinate b) (productChartCoordinate c) t

/-- The smooth polynomial domain is open in the original input chart. -/
instance smoothPolynomialInput_isOpenImmersion (b c : Bool) (t : Fin 3) :
    IsOpenImmersion (smoothPolynomialInput W b c t) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The original polynomial domain restricted inside the smooth input chart product. -/
def smoothPolynomialToInputs (b c : Bool) (t : Fin 3) :
    (polynomialSmoothInputOpen W (productChartCoordinate b) (productChartCoordinate c)
      t).toScheme ⟶ (smoothProductChartOpen W b c).toScheme :=
  IsOpenImmersion.lift (smoothProductChartOpen W b c).ι (smoothPolynomialInput W b c t) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    exact (polynomialSmoothInputOpen_preimage W b c t).ge p.property)

/-- The restricted polynomial input morphism preserves the original product inclusion. -/
@[reassoc] theorem smoothPolynomialToInputs_inclusion (b c : Bool) (t : Fin 3) :
    smoothPolynomialToInputs W b c t ≫ (smoothProductChartOpen W b c).ι =
      smoothPolynomialInput W b c t :=
  IsOpenImmersion.lift_fac _ _ _

/-- The polynomial smooth domain remains an open immersion after restriction. -/
instance smoothPolynomialToInputs_isOpenImmersion (b c : Bool) (t : Fin 3) :
    IsOpenImmersion (smoothPolynomialToInputs W b c t) :=
  inferInstanceAs (IsOpenImmersion (IsOpenImmersion.lift _ _ _))

end FLT.Mazur.WeierstrassIntegralChart
