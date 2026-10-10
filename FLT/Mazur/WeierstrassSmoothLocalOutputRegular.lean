/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRegularChartSectionDescent
public import FLT.Mazur.WeierstrassSmoothTransportedCover

/-!
# Regular outputs on the original smooth affine formula domains

The smooth cover projections are open immersions to the original domains.
Their regular output coordinates therefore survive every flat restriction.
An arbitrary Y/Z presentation of the same smooth sum inherits regularity.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Projection to the original affine formula domain is an open immersion. -/
instance smoothAffineAdditionProjection_isOpenImmersion (i : AdditionChartIndex) :
    IsOpenImmersion (smoothAffineAdditionProjection W i) := by
  dsimp [smoothAffineAdditionProjection, Scheme.Cover.pullbackHom]
  infer_instance

/-- The original chart output is the actual local smooth output. -/
theorem smoothAffineLocal_chart_output (i : AdditionChartIndex) :
    smoothAffineAdditionLocal W i ≫ (integralSmoothOpen W).ι =
      smoothAffineAdditionProjection W i ≫
        Spec.map (CommRingCat.ofHom (additionChartAlgOutput W i).toRingHom) ≫
          integralCurveChart W (additionChartOutput i) := by
  rw [smoothAffineAdditionLocal, Category.assoc, additionSmoothChart_inclusion,
    smoothAffineAdditionLift_inclusion_assoc]
  rw [additionCurveChart, additionChartAlgOutput_spec]

/-- Every flat restriction of a smooth affine formula has regular normalized output Z. -/
theorem smoothAffineLocal_output_z_regular (i : AdditionChartIndex)
    {X : Scheme.{u}} (f : X ⟶ (smoothAffineAdditionCover W).X i) [Flat f] :
    IsRegular (specSectionHom
      (f ≫ smoothAffineAdditionProjection W i ≫
        Spec.map (CommRingCat.ofHom (additionChartAlgOutput W i).toRingHom))
      (coord W (additionChartOutput i) 2)) := by
  rw [← Category.assoc, specSectionHom_comp]
  exact additionChart_output_z_regular_sections W i (f ≫ smoothAffineAdditionProjection W i)

/-- Regular output transfers to any Y/Z presentation of a flat local smooth sum. -/
theorem smoothAffineLocal_z_regular (i : AdditionChartIndex)
    {X : Scheme.{u}} (f : X ⟶ (smoothAffineAdditionCover W).X i) [Flat f]
    (b : Bool) (p : X ⟶ chartScheme W (productChartCoordinate b))
    (hp : p ≫ integralCurveChart W (productChartCoordinate b) =
      f ≫ smoothAffineAdditionLocal W i ≫ (integralSmoothOpen W).ι) :
    IsRegular (specSectionHom p (coord W (productChartCoordinate b) 2)) := by
  apply chart_z_regular_of_global_eq W b (additionChartOutput i)
    (by cases i <;> simp [additionChartOutput])
    p (f ≫ smoothAffineAdditionProjection W i ≫
      Spec.map (CommRingCat.ofHom (additionChartAlgOutput W i).toRingHom))
  · simpa only [Category.assoc, smoothAffineLocal_chart_output] using hp
  · exact smoothAffineLocal_output_z_regular W i f

/-- Every Y/Z presentation of a flat restriction of full smooth affine addition has regular Z. -/
theorem smoothAffineAddition_z_regular {X : Scheme.{u}}
    (f : X ⟶ (smoothAffineInputOpen W).toScheme) [Flat f]
    (b : Bool) (p : X ⟶ chartScheme W (productChartCoordinate b))
    (hp : p ≫ integralCurveChart W (productChartCoordinate b) =
      f ≫ smoothAffineAddition W ≫ (integralSmoothOpen W).ι) :
    IsRegular (specSectionHom p (coord W (productChartCoordinate b) 2)) := by
  let C := smoothAffineAdditionCover W
  apply specSectionHom_isRegular_of_cover (C.pullback₁ f)
  intro i
  let u := (C.pullback₁ f).f i
  let v := Scheme.Cover.pullbackHom C f i
  have hv : Flat v := by dsimp [v, Scheme.Cover.pullbackHom]; infer_instance
  apply smoothAffineLocal_z_regular W i v b (u ≫ p)
  rw [Category.assoc, hp, ← Category.assoc u f]
  have he : v ≫ C.f i = u ≫ f := Scheme.Cover.pullbackHom_map C f i
  rw [← he, Category.assoc, smoothAffineAdditionLocal_glued_assoc]

end FLT.Mazur.WeierstrassIntegralChart
