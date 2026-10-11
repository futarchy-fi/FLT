/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothTransportedOutputRegular

/-!
# Regular outputs on every left smooth input chart

The genuine mixed and Y/Y covers descend regularity from the original local
formulas, retaining singular second inputs and arbitrary coefficient rings.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Projection to an original mixed formula domain is open. -/
instance leftSmoothMixedProjection_isOpenImmersion (b c : Bool)
    (ha : b = false ∨ c = false) (i : Bool) :
    IsOpenImmersion (leftSmoothMixedProjection W b c ha i) := by
  dsimp [leftSmoothMixedProjection]
  infer_instance

/-- The mixed affine lift is an open immersion. -/
instance leftSmoothMixedAffineLift_isOpenImmersion (b c : Bool)
    (ha : b = false ∨ c = false) :
    IsOpenImmersion (leftSmoothMixedAffineLift W b c ha) := by
  dsimp [leftSmoothMixedAffineLift]
  infer_instance

/-- Projection to an original Y/Y formula domain is open. -/
instance leftSmoothYProjection_isOpenImmersion (i : YProductCoverIndex) :
    IsOpenImmersion (leftSmoothYProjection W i) := by
  dsimp [leftSmoothYProjection]
  infer_instance

/-- The Y/Y affine lift is an open immersion. -/
instance leftSmoothYAffineLift_isOpenImmersion :
    IsOpenImmersion (leftSmoothYAffineLift W) := by
  dsimp [leftSmoothYAffineLift]
  infer_instance

/-- The full mixed law has regular Z on every flat Y/Z presentation. -/
theorem leftSmoothMixedAddition_z_regular (b c : Bool) (ha : b = false ∨ c = false)
    {X : Scheme.{u}} (f : X ⟶ (leftSmoothProductChartOpen W b c).toScheme) [Flat f]
    (d : Bool) (p : X ⟶ chartScheme W (productChartCoordinate d))
    (hp : p ≫ integralCurveChart W (productChartCoordinate d) =
      f ≫ leftSmoothMixedAddition W b c ha) :
    IsRegular (specSectionHom p (coord W (productChartCoordinate d) 2)) := by
  let C := leftSmoothMixedCover W b c ha
  apply specSectionHom_isRegular_of_cover (C.pullback₁ f)
  intro i
  let u := (C.pullback₁ f).f i
  let v := Scheme.Cover.pullbackHom C f i
  have hv : Flat v := by dsimp [v, Scheme.Cover.pullbackHom]; infer_instance
  have he : v ≫ C.f i = u ≫ f := Scheme.Cover.pullbackHom_map C f i
  have hh : (u ≫ p) ≫ integralCurveChart W (productChartCoordinate d) =
      v ≫ leftSmoothMixedLocal W b c ha i := by
    rw [Category.assoc, hp, ← Category.assoc u f, ← he, Category.assoc]
    exact congrArg (fun q => v ≫ q)
      (leftSmoothMixedLocal_glued W b c ha i)
  cases i
  · exact projectiveAdditionChart_z_regular W _ _
      (v ≫ leftSmoothMixedProjection W b c ha false) d (u ≫ p) hh
  · exact leftSmoothAffineOverlapAddition_z_regular W b c
      (v ≫ leftSmoothMixedAffineLift W b c ha) d (u ≫ p) hh

/-- The full Y/Y law has regular Z on every flat Y/Z presentation. -/
theorem leftSmoothYAddition_z_regular {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothProductChartOpen W true true).toScheme) [Flat f]
    (d : Bool) (p : X ⟶ chartScheme W (productChartCoordinate d))
    (hp : p ≫ integralCurveChart W (productChartCoordinate d) =
      f ≫ leftSmoothYAddition W) :
    IsRegular (specSectionHom p (coord W (productChartCoordinate d) 2)) := by
  let C := leftSmoothYCover W
  apply specSectionHom_isRegular_of_cover (C.pullback₁ f)
  intro i
  let u := (C.pullback₁ f).f i
  let v := Scheme.Cover.pullbackHom C f i
  have hv : Flat v := by dsimp [v, Scheme.Cover.pullbackHom]; infer_instance
  have he : v ≫ C.f i = u ≫ f := Scheme.Cover.pullbackHom_map C f i
  have hh : (u ≫ p) ≫ integralCurveChart W (productChartCoordinate d) =
      v ≫ leftSmoothYLocal W i := by
    rw [Category.assoc, hp, ← Category.assoc u f, ← he, Category.assoc]
    exact congrArg (fun q => v ≫ q) (leftSmoothYLocal_glued W i)
  cases i
  · exact leftSmoothAffineOverlapAddition_z_regular W true true
      (v ≫ leftSmoothYAffineLift W) d (u ≫ p) hh
  · exact projectiveAdditionChart_z_regular W 1 1
      (v ≫ leftSmoothYProjection W .polynomial) d (u ≫ p) hh
  · exact infinityAdditionSpec_z_regular W
      (v ≫ leftSmoothYProjection W .infinity) d (u ≫ p) hh

/-- Every left smooth input-chart law has regular output Z after a flat source restriction. -/
theorem leftSmoothInputAddition_z_regular (b c : Bool) {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothProductChartOpen W b c).toScheme) [Flat f]
    (d : Bool) (p : X ⟶ chartScheme W (productChartCoordinate d))
    (hp : p ≫ integralCurveChart W (productChartCoordinate d) =
      f ≫ leftSmoothInputAddition W b c) :
    IsRegular (specSectionHom p (coord W (productChartCoordinate d) 2)) := by
  cases b <;> cases c
  · exact leftSmoothMixedAddition_z_regular W false false (.inl rfl) f d p hp
  · exact leftSmoothMixedAddition_z_regular W false true (.inl rfl) f d p hp
  · exact leftSmoothMixedAddition_z_regular W true false (.inr rfl) f d p hp
  · exact leftSmoothYAddition_z_regular W f d p hp

end FLT.Mazur.WeierstrassIntegralChart
