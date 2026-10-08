/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothInputOutputRegular
public import FLT.Mazur.WeierstrassSmoothTripleInputRegular

/-!
# Regular coordinates of the full smooth addition output

The full product cover descends regularity from the original formulas.
Consequently both intermediate sums of a flat smooth triple have regular
Z in every Y/Z presentation, without a flatness assumption on addition.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The full smooth product cover projects openly to its original tensor chart. -/
instance smoothCurveProductCoverProjection_isOpenImmersion (b c : Bool) :
    IsOpenImmersion (smoothCurveProductCoverProjection W b c) := by
  dsimp [smoothCurveProductCoverProjection, Scheme.Cover.pullbackHom]
  infer_instance

/-- Restricting the projection to the smooth tensor chart preserves its open immersion. -/
instance smoothCurveProductCoverToChart_isOpenImmersion (b c : Bool) :
    IsOpenImmersion (smoothCurveProductCoverToChart W b c) := by
  dsimp [smoothCurveProductCoverToChart]
  infer_instance

/-- Regularity holds on every Y/Z presentation of a flat restriction of the full smooth law. -/
theorem smoothCurveAddition_z_regular {X : Scheme.{u}}
    (f : X ⟶ (smoothCurveProductOpen W).toScheme) [Flat f]
    (d : Bool) (p : X ⟶ chartScheme W (productChartCoordinate d))
    (hp : p ≫ integralCurveChart W (productChartCoordinate d) =
      f ≫ smoothCurveAddition W ≫ (integralSmoothOpen W).ι) :
    IsRegular (specSectionHom p (coord W (productChartCoordinate d) 2)) := by
  let C := smoothCurveProductCover W
  apply specSectionHom_isRegular_of_cover (C.pullback₁ f)
  rintro ⟨b, c⟩
  let u := (C.pullback₁ f).f (b, c)
  let v := Scheme.Cover.pullbackHom C f (b, c)
  have hv : Flat v := by dsimp [v, Scheme.Cover.pullbackHom]; infer_instance
  apply smoothInputAddition_z_regular W b c (v ≫ smoothCurveProductCoverToChart W b c)
    d (u ≫ p)
  have he : v ≫ C.f (b, c) = u ≫ f := Scheme.Cover.pullbackHom_map C f (b, c)
  rw [Category.assoc, hp, ← Category.assoc u f, ← he]
  simp only [Category.assoc]
  exact congrArg (fun q => v ≫ q ≫ (integralSmoothOpen W).ι)
    (smoothCurveProductCover_addition W b c)

/-- The categorical product comparison is an open immersion, since it is an isomorphism. -/
instance smoothFactorsToProduct_isOpenImmersion :
    IsOpenImmersion (smoothFactorsToProduct W) :=
  inferInstanceAs (IsOpenImmersion (smoothProductFactorsIso W).inv)

/-- The categorical smooth law has regular output on every flat Y/Z presentation. -/
theorem smoothFactorAddition_z_regular {X : Scheme.{u}}
    (f : X ⟶ smoothFactorProduct W) [Flat f]
    (d : Bool) (p : X ⟶ chartScheme W (productChartCoordinate d))
    (hp : p ≫ integralCurveChart W (productChartCoordinate d) =
      f ≫ smoothFactorAddition W ≫ (integralSmoothOpen W).ι) :
    IsRegular (specSectionHom p (coord W (productChartCoordinate d) 2)) := by
  apply smoothCurveAddition_z_regular W (f ≫ smoothFactorsToProduct W) d p
  simpa only [smoothFactorAddition, Category.assoc] using hp

/-- The first intermediate sum has regular Z on every flat triple restriction. -/
theorem smoothTripleFirstSum_z_regular {X : Scheme.{u}}
    (t : X ⟶ smoothFactorTriple W) [Flat t]
    (d : Bool) (p : X ⟶ chartScheme W (productChartCoordinate d))
    (hp : p ≫ integralCurveChart W (productChartCoordinate d) =
      t ≫ smoothFactorTriplePair W ≫ smoothFactorAddition W ≫ (integralSmoothOpen W).ι) :
    IsRegular (specSectionHom p (coord W (productChartCoordinate d) 2)) :=
  smoothFactorAddition_z_regular W (t ≫ smoothFactorTriplePair W) d p hp

/-- The second intermediate sum has regular Z on every flat triple restriction. -/
theorem smoothTripleLastSum_z_regular {X : Scheme.{u}}
    (t : X ⟶ smoothFactorTriple W) [Flat t]
    (d : Bool) (p : X ⟶ chartScheme W (productChartCoordinate d))
    (hp : p ≫ integralCurveChart W (productChartCoordinate d) =
      t ≫ smoothFactorTripleLastPair W ≫ smoothFactorAddition W ≫ (integralSmoothOpen W).ι) :
    IsRegular (specSectionHom p (coord W (productChartCoordinate d) 2)) :=
  smoothFactorAddition_z_regular W (t ≫ smoothFactorTripleLastPair W) d p hp

end FLT.Mazur.WeierstrassIntegralChart
