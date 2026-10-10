/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothLocalOutputRegular
public import FLT.Mazur.WeierstrassSmoothInputAddition

/-!
# Regular outputs for transported, polynomial and infinity smooth laws

Regularity is proved on the original restricted formula domains. The output
may be presented in either Y or Z, independently of the formula's own chart.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Simultaneous normalization of smooth inputs is an open immersion. -/
instance smoothAffineOverlapToInputs_isOpenImmersion (b c : Bool) :
    IsOpenImmersion (smoothAffineOverlapToInputs W b c) := by
  dsimp [smoothAffineOverlapToInputs]
  infer_instance

/-- Transported smooth affine addition retains regular Z under flat restriction. -/
theorem smoothAffineOverlapAddition_z_regular (b c : Bool) {X : Scheme.{u}}
    (f : X ⟶ (smoothAffineOverlapOpen W b c).toScheme) [Flat f]
    (d : Bool) (p : X ⟶ chartScheme W (productChartCoordinate d))
    (hp : p ≫ integralCurveChart W (productChartCoordinate d) =
      f ≫ smoothAffineOverlapAddition W b c ≫ (integralSmoothOpen W).ι) :
    IsRegular (specSectionHom p (coord W (productChartCoordinate d) 2)) := by
  apply smoothAffineAddition_z_regular W (f ≫ smoothAffineOverlapToInputs W b c) d p
  simpa only [smoothAffineOverlapAddition, Category.assoc] using hp

/-- A polynomial output-Z formula has regular Z in every other Y/Z presentation. -/
theorem polynomialSmoothChart_z_regular (j k : Fin 3) {X : Scheme.{u}}
    (f : X ⟶ (polynomialSmoothInputOpen W j k 2).toScheme)
    (b : Bool) (p : X ⟶ chartScheme W (productChartCoordinate b))
    (hp : p ≫ integralCurveChart W (productChartCoordinate b) =
      f ≫ polynomialSmoothChart W j k 2 ≫ (integralSmoothOpen W).ι) :
    IsRegular (specSectionHom p (coord W (productChartCoordinate b) 2)) := by
  apply chart_z_regular_of_global_eq W b 2 (.inr rfl) p
    (f ≫ (polynomialSmoothInputOpen W j k 2).ι ≫
      Spec.map (CommRingCat.ofHom (projectiveAdditionChart W j k 2).toRingHom))
  · simpa only [Category.assoc, polynomialSmoothChart_inclusion] using hp
  · exact affineOutput_z_regular W _

/-- The original infinity formula retains its regular output on every flat smooth restriction. -/
theorem infinitySmoothChart_z_regular {X : Scheme.{u}}
    (f : X ⟶ (infinitySmoothInputOpen W).toScheme) [Flat f]
    (b : Bool) (p : X ⟶ chartScheme W (productChartCoordinate b))
    (hp : p ≫ integralCurveChart W (productChartCoordinate b) =
      f ≫ infinitySmoothChart W ≫ (integralSmoothOpen W).ι) :
    IsRegular (specSectionHom p (coord W (productChartCoordinate b) 2)) := by
  apply chart_z_regular_of_global_eq W b 1 (.inl rfl) p
    (f ≫ (infinitySmoothInputOpen W).ι ≫
      Spec.map (CommRingCat.ofHom (infinityAdditionChart W).toRingHom))
  · simpa only [Category.assoc, infinitySmoothChart_inclusion] using hp
  · rw [← Category.assoc, specSectionHom_comp]
    exact specSectionHom_isRegular (f ≫ (infinitySmoothInputOpen W).ι)
      (infinityAdditionChart_z_regular W)

end FLT.Mazur.WeierstrassIntegralChart
