/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothTransportedOutputRegular

/-!
# Regular outputs on all four full smooth input charts

The actual mixed and Y/Y covers descend regularity from the original local
formulas. This proves regularity for flat restrictions of each entire smooth
input chart without assuming that addition is flat.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The full mixed law has regular Z on every flat Y/Z presentation. -/
theorem smoothMixedAddition_z_regular (b c : Bool) (ha : b = false ∨ c = false)
    {X : Scheme.{u}} (f : X ⟶ (smoothProductChartOpen W b c).toScheme) [Flat f]
    (d : Bool) (p : X ⟶ chartScheme W (productChartCoordinate d))
    (hp : p ≫ integralCurveChart W (productChartCoordinate d) =
      f ≫ smoothMixedAddition W b c ha ≫ (integralSmoothOpen W).ι) :
    IsRegular (specSectionHom p (coord W (productChartCoordinate d) 2)) := by
  let C := smoothMixedCover W b c ha
  apply specSectionHom_isRegular_of_cover (C.pullback₁ f)
  intro i
  let u := (C.pullback₁ f).f i
  let v := Scheme.Cover.pullbackHom C f i
  have hv : Flat v := by dsimp [v, Scheme.Cover.pullbackHom]; infer_instance
  have he : v ≫ C.f i = u ≫ f := Scheme.Cover.pullbackHom_map C f i
  have hh : (u ≫ p) ≫ integralCurveChart W (productChartCoordinate d) =
      v ≫ smoothMixedLocal W b c i ≫ (integralSmoothOpen W).ι := by
    rw [Category.assoc, hp, ← Category.assoc u f, ← he, Category.assoc]
    exact congrArg (fun q => v ≫ q ≫ (integralSmoothOpen W).ι)
      (smoothMixedLocal_glued W b c ha i)
  cases i
  · exact polynomialSmoothChart_z_regular W _ _ v d (u ≫ p) hh
  · exact smoothAffineOverlapAddition_z_regular W b c v d (u ≫ p) hh

/-- The full Y/Y law has regular Z on every flat Y/Z presentation. -/
theorem smoothYAddition_z_regular {X : Scheme.{u}}
    (f : X ⟶ (smoothProductChartOpen W true true).toScheme) [Flat f]
    (d : Bool) (p : X ⟶ chartScheme W (productChartCoordinate d))
    (hp : p ≫ integralCurveChart W (productChartCoordinate d) =
      f ≫ smoothYAddition W ≫ (integralSmoothOpen W).ι) :
    IsRegular (specSectionHom p (coord W (productChartCoordinate d) 2)) := by
  let C := smoothYCover W
  apply specSectionHom_isRegular_of_cover (C.pullback₁ f)
  intro i
  let u := (C.pullback₁ f).f i
  let v := Scheme.Cover.pullbackHom C f i
  have hv : Flat v := by dsimp [v, Scheme.Cover.pullbackHom]; infer_instance
  have he : v ≫ C.f i = u ≫ f := Scheme.Cover.pullbackHom_map C f i
  have hh : (u ≫ p) ≫ integralCurveChart W (productChartCoordinate d) =
      v ≫ smoothYLocal W i ≫ (integralSmoothOpen W).ι := by
    rw [Category.assoc, hp, ← Category.assoc u f, ← he, Category.assoc]
    exact congrArg (fun q => v ≫ q ≫ (integralSmoothOpen W).ι) (smoothYLocal_glued W i)
  cases i
  · exact smoothAffineOverlapAddition_z_regular W true true v d (u ≫ p) hh
  · exact polynomialSmoothChart_z_regular W 1 1 v d (u ≫ p) hh
  · exact infinitySmoothChart_z_regular W v d (u ≫ p) hh

/-- Every full smooth input-chart law has regular output Z after a flat source restriction. -/
theorem smoothInputAddition_z_regular (b c : Bool) {X : Scheme.{u}}
    (f : X ⟶ (smoothProductChartOpen W b c).toScheme) [Flat f]
    (d : Bool) (p : X ⟶ chartScheme W (productChartCoordinate d))
    (hp : p ≫ integralCurveChart W (productChartCoordinate d) =
      f ≫ smoothInputAddition W b c ≫ (integralSmoothOpen W).ι) :
    IsRegular (specSectionHom p (coord W (productChartCoordinate d) 2)) := by
  cases b <;> cases c
  · exact smoothMixedAddition_z_regular W false false (.inl rfl) f d p hp
  · exact smoothMixedAddition_z_regular W false true (.inl rfl) f d p hp
  · exact smoothMixedAddition_z_regular W true false (.inr rfl) f d p hp
  · exact smoothYAddition_z_regular W f d p hp

end FLT.Mazur.WeierstrassIntegralChart
