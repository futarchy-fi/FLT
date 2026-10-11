/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothInputOutputRegular
public import FLT.Mazur.WeierstrassLeftSmoothTripleInputRegular

/-!
# Regular output coordinates for translation on the whole cubic

The original projective input cover descends regularity of the enlarged law.
In particular the second intermediate action sum has regular Z on every flat
Y/Z presentation, without assuming flatness of addition.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The full smooth product cover projects openly to its original tensor chart. -/
instance leftSmoothCurveProductCoverProjection_isOpenImmersion (b c : Bool) :
    IsOpenImmersion (leftSmoothCurveProductCoverProjection W b c) := by
  dsimp [leftSmoothCurveProductCoverProjection, Scheme.Cover.pullbackHom]
  infer_instance

/-- Restricting the projection to the left smooth tensor chart preserves its open immersion. -/
instance leftSmoothCurveProductCoverToChart_isOpenImmersion (b c : Bool) :
    IsOpenImmersion (leftSmoothCurveProductCoverToChart W b c) := by
  dsimp [leftSmoothCurveProductCoverToChart]
  infer_instance

/-- Regularity holds on every Y/Z presentation of a flat restriction of the enlarged law. -/
theorem leftSmoothCurveAddition_z_regular {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothCurveProductOpen W).toScheme) [Flat f]
    (d : Bool) (p : X ⟶ chartScheme W (productChartCoordinate d))
    (hp : p ≫ integralCurveChart W (productChartCoordinate d) =
      f ≫ leftSmoothCurveAddition W) :
    IsRegular (specSectionHom p (coord W (productChartCoordinate d) 2)) := by
  let C := leftSmoothCurveProductCover W
  apply specSectionHom_isRegular_of_cover (C.pullback₁ f)
  rintro ⟨b, c⟩
  let u := (C.pullback₁ f).f (b, c)
  let v := Scheme.Cover.pullbackHom C f (b, c)
  have hv : Flat v := by dsimp [v, Scheme.Cover.pullbackHom]; infer_instance
  apply leftSmoothInputAddition_z_regular W b c (v ≫ leftSmoothCurveProductCoverToChart W b c)
    d (u ≫ p)
  have he : v ≫ C.f (b, c) = u ≫ f := Scheme.Cover.pullbackHom_map C f (b, c)
  rw [Category.assoc, hp, ← Category.assoc u f, ← he]
  simp only [Category.assoc]
  exact congrArg (fun q => v ≫ q)
    (leftSmoothCurveProductCover_addition W b c)

/-- The categorical product comparison is an open immersion, since it is an isomorphism. -/
instance leftSmoothFactorsToProduct_isOpenImmersion :
    IsOpenImmersion (leftSmoothFactorsToProduct W) :=
  inferInstanceAs (IsOpenImmersion (leftSmoothProductFactorsIso W).inv)

/-- The categorical enlarged law has regular output on every flat Y/Z presentation. -/
theorem leftSmoothFactorAddition_z_regular {X : Scheme.{u}}
    (f : X ⟶ leftSmoothFactorProduct W) [Flat f]
    (d : Bool) (p : X ⟶ chartScheme W (productChartCoordinate d))
    (hp : p ≫ integralCurveChart W (productChartCoordinate d) =
      f ≫ leftSmoothFactorAddition W) :
    IsRegular (specSectionHom p (coord W (productChartCoordinate d) 2)) := by
  apply leftSmoothCurveAddition_z_regular W (f ≫ leftSmoothFactorsToProduct W) d p
  simpa only [leftSmoothFactorAddition, Category.assoc] using hp

/-- The second intermediate sum has regular Z on every flat triple restriction. -/
theorem leftSmoothTripleLastSum_z_regular {X : Scheme.{u}}
    (t : X ⟶ leftSmoothTriple W) [Flat t]
    (d : Bool) (p : X ⟶ chartScheme W (productChartCoordinate d))
    (hp : p ≫ integralCurveChart W (productChartCoordinate d) =
      t ≫ leftSmoothTripleLastPair W ≫ leftSmoothFactorAddition W) :
    IsRegular (specSectionHom p (coord W (productChartCoordinate d) 2)) :=
  leftSmoothFactorAddition_z_regular W (t ≫ leftSmoothTripleLastPair W) d p hp

end FLT.Mazur.WeierstrassIntegralChart
