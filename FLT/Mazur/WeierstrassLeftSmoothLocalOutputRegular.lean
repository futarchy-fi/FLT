/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRegularChartSectionDescent
public import FLT.Mazur.WeierstrassLeftSmoothAffineAddition

/-!
# Regular output coordinates with an arbitrary second affine input

The actual four affine formulas retain regular output Z under flat restriction.
Their cover descends this property to the enlarged affine law.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The enlarged affine domain inclusion is an open immersion. -/
instance leftSmoothAffineInputToDomain_isOpenImmersion :
    IsOpenImmersion (leftSmoothAffineInputToDomain W) := by
  dsimp [leftSmoothAffineInputToDomain]
  infer_instance

/-- The pulled-back cover retains open projections to the original formula rings. -/
instance leftSmoothAffineAdditionProjection_isOpenImmersion (i : AdditionChartIndex) :
    IsOpenImmersion (leftSmoothAffineAdditionProjection W i) := by
  dsimp [leftSmoothAffineAdditionProjection, Scheme.Cover.pullbackHom]
  infer_instance

/-- A flat restriction of any original affine formula has regular Z in every Y/Z chart. -/
theorem additionCurveChart_z_regular (i : AdditionChartIndex) {X : Scheme.{u}}
    (f : X ⟶ Spec (additionChartRing W i)) [Flat f]
    (b : Bool) (p : X ⟶ chartScheme W (productChartCoordinate b))
    (hp : p ≫ integralCurveChart W (productChartCoordinate b) =
      f ≫ additionCurveChart W i) :
    IsRegular (specSectionHom p (coord W (productChartCoordinate b) 2)) := by
  apply chart_z_regular_of_global_eq W b (additionChartOutput i)
    (by cases i <;> simp [additionChartOutput]) p
    (f ≫ Spec.map (CommRingCat.ofHom (additionChartAlgOutput W i).toRingHom))
  · simpa only [Category.assoc, additionCurveChart, additionChartAlgOutput_spec] using hp
  · rw [specSectionHom_comp]
    exact additionChart_output_z_regular_sections W i f

/-- The enlarged affine law has regular Z after every flat restriction. -/
theorem leftSmoothAffineAddition_z_regular {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothAffineInputOpen W).toScheme) [Flat f]
    (b : Bool) (p : X ⟶ chartScheme W (productChartCoordinate b))
    (hp : p ≫ integralCurveChart W (productChartCoordinate b) =
      f ≫ leftSmoothAffineAddition W) :
    IsRegular (specSectionHom p (coord W (productChartCoordinate b) 2)) := by
  let C := leftSmoothAffineAdditionCover W
  apply specSectionHom_isRegular_of_cover (C.pullback₁ f)
  intro i
  let u := (C.pullback₁ f).f i
  let v := Scheme.Cover.pullbackHom C f i
  have hv : Flat v := by dsimp [v, Scheme.Cover.pullbackHom]; infer_instance
  apply additionCurveChart_z_regular W i (v ≫ leftSmoothAffineAdditionProjection W i)
    b (u ≫ p)
  rw [Category.assoc, hp, Category.assoc, leftSmoothAffineAdditionProjection_addition]
  have he : v ≫ C.f i = u ≫ f := Scheme.Cover.pullbackHom_map C f i
  simpa only [Category.assoc] using
    congrArg (fun q => q ≫ leftSmoothAffineAddition W) he.symm

end FLT.Mazur.WeierstrassIntegralChart
