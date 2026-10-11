/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothLocalOutputRegular
public import FLT.Mazur.WeierstrassLeftSmoothInputAddition

/-!
# Regular output coordinates on the original enlarged formula domains

Affine normalization and the original polynomial and infinity formulas retain
regular Z, without requiring that the second input or output be smooth.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Normalization of the enlarged affine overlap is an open immersion. -/
instance leftSmoothAffineOverlapToInputs_isOpenImmersion (b c : Bool) :
    IsOpenImmersion (leftSmoothAffineOverlapToInputs W b c) := by
  dsimp [leftSmoothAffineOverlapToInputs]
  infer_instance

/-- Transported enlarged affine addition retains regular Z under flat restriction. -/
theorem leftSmoothAffineOverlapAddition_z_regular (b c : Bool) {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothAffineOverlapOpen W b c).toScheme) [Flat f]
    (d : Bool) (p : X ⟶ chartScheme W (productChartCoordinate d))
    (hp : p ≫ integralCurveChart W (productChartCoordinate d) =
      f ≫ leftSmoothAffineOverlapAddition W b c) :
    IsRegular (specSectionHom p (coord W (productChartCoordinate d) 2)) := by
  apply leftSmoothAffineAddition_z_regular W (f ≫ leftSmoothAffineOverlapToInputs W b c) d p
  simpa only [leftSmoothAffineOverlapAddition, Category.assoc] using hp

/-- A polynomial output-Z formula has regular Z in every other Y/Z presentation. -/
theorem projectiveAdditionChart_z_regular (j k : Fin 3) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (AdditionOutputOpen W j k 2)))
    (b : Bool) (p : X ⟶ chartScheme W (productChartCoordinate b))
    (hp : p ≫ integralCurveChart W (productChartCoordinate b) =
      f ≫ Spec.map (CommRingCat.ofHom (projectiveAdditionChart W j k 2).toRingHom) ≫
        integralCurveChart W 2) :
    IsRegular (specSectionHom p (coord W (productChartCoordinate b) 2)) := by
  apply chart_z_regular_of_global_eq W b 2 (.inr rfl) p
    (f ≫ Spec.map (CommRingCat.ofHom (projectiveAdditionChart W j k 2).toRingHom))
  · simpa only [Category.assoc] using hp
  · exact affineOutput_z_regular W _

/-- The original infinity formula has regular Z under every flat restriction. -/
theorem infinityAdditionSpec_z_regular {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (InfinityAdditionOpen W))) [Flat f]
    (b : Bool) (p : X ⟶ chartScheme W (productChartCoordinate b))
    (hp : p ≫ integralCurveChart W (productChartCoordinate b) =
      f ≫ infinityAdditionSpec W ≫ integralCurveChart W 1) :
    IsRegular (specSectionHom p (coord W (productChartCoordinate b) 2)) := by
  apply chart_z_regular_of_global_eq W b 1 (.inl rfl) p (f ≫ infinityAdditionSpec W)
  · simpa only [Category.assoc] using hp
  · rw [infinityAdditionSpec, specSectionHom_comp]
    exact specSectionHom_isRegular f (infinityAdditionChart_z_regular W)

end FLT.Mazur.WeierstrassIntegralChart
